%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  401 (1146 expanded)
%              Number of leaves         :   58 ( 473 expanded)
%              Depth                    :   28
%              Number of atoms          : 3002 (6093 expanded)
%              Number of equality atoms :  228 ( 549 expanded)
%              Maximal formula depth    :   26 (   9 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1020,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f96,f103,f107,f114,f118,f122,f131,f160,f164,f170,f185,f205,f209,f324,f352,f356,f362,f370,f374,f378,f386,f390,f497,f565,f620,f635,f639,f665,f726,f734,f752,f773,f817,f835,f898,f926,f950,f988,f995,f1011,f1019])).

fof(f1019,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_22
    | ~ spl6_23
    | ~ spl6_78
    | ~ spl6_92
    | ~ spl6_96 ),
    inference(avatar_contradiction_clause,[],[f1018])).

fof(f1018,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_22
    | ~ spl6_23
    | ~ spl6_78
    | ~ spl6_92
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f1017,f993])).

fof(f993,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_23
    | ~ spl6_92
    | ~ spl6_96 ),
    inference(forward_demodulation,[],[f990,f925])).

fof(f925,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f924])).

fof(f924,plain,
    ( spl6_92
  <=> k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f990,plain,
    ( k7_relat_1(sK4,sK3) = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_23
    | ~ spl6_96 ),
    inference(superposition,[],[f211,f987])).

fof(f987,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK4),sK3)
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f986])).

fof(f986,plain,
    ( spl6_96
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f211,plain,
    ( ! [X1] : k7_relat_1(sK4,X1) = k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X1))
    | ~ spl6_23 ),
    inference(resolution,[],[f208,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f208,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl6_23
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f1017,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_22
    | ~ spl6_78 ),
    inference(forward_demodulation,[],[f1016,f834])).

fof(f834,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f833])).

fof(f833,plain,
    ( spl6_78
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1016,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_22 ),
    inference(forward_demodulation,[],[f1015,f192])).

fof(f192,plain,
    ( ! [X0] : k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl6_2
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f187,f75])).

fof(f75,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_2
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) )
    | ~ spl6_17 ),
    inference(resolution,[],[f169,f53])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f169,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_17
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f1015,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | spl6_22 ),
    inference(forward_demodulation,[],[f1014,f159])).

fof(f159,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl6_15
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1014,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_12
    | ~ spl6_16
    | spl6_22 ),
    inference(forward_demodulation,[],[f1013,f137])).

fof(f137,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)
    | ~ spl6_12 ),
    inference(resolution,[],[f121,f54])).

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

fof(f121,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f1013,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_16
    | spl6_22 ),
    inference(forward_demodulation,[],[f204,f181])).

fof(f181,plain,
    ( ! [X0] : k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | ~ spl6_1
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f176,f71])).

fof(f71,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_1
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK5)
        | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) )
    | ~ spl6_16 ),
    inference(resolution,[],[f163,f53])).

fof(f163,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl6_16
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f204,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl6_22
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f1011,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_21
    | ~ spl6_23
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_78
    | ~ spl6_92
    | ~ spl6_96 ),
    inference(avatar_contradiction_clause,[],[f1010])).

fof(f1010,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_21
    | ~ spl6_23
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_78
    | ~ spl6_92
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f201,f1009])).

fof(f1009,plain,
    ( sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_78
    | ~ spl6_92
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f998,f993])).

fof(f998,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44
    | ~ spl6_78 ),
    inference(forward_demodulation,[],[f529,f834])).

fof(f529,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f528,f192])).

fof(f528,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f527,f159])).

fof(f527,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f526,f137])).

fof(f526,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f525,f181])).

fof(f525,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f524,f91])).

fof(f91,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f524,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f523,f369])).

fof(f369,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f368])).

fof(f368,plain,
    ( spl6_40
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f523,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_36
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f522,f351])).

fof(f351,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl6_36
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f522,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f521,f163])).

fof(f521,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f520,f106])).

fof(f106,plain,
    ( v1_funct_2(sK5,sK3,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_9
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f520,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f519,f71])).

% (5798)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f519,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f518,f169])).

fof(f518,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f517,f113])).

fof(f113,plain,
    ( v1_funct_2(sK4,sK2,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_10
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f517,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f516,f75])).

fof(f516,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f515,f121])).

fof(f515,plain,
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
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f514,f79])).

fof(f79,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_3
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f514,plain,
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
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f513,f130])).

fof(f130,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f513,plain,
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
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f512,f83])).

% (5781)Refutation not found, incomplete strategy% (5781)------------------------------
% (5781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5781)Termination reason: Refutation not found, incomplete strategy

% (5781)Memory used [KB]: 10746
% (5781)Time elapsed: 0.112 s
% (5781)------------------------------
% (5781)------------------------------
% (5795)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f83,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f512,plain,
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
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f498,f87])).

fof(f87,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f498,plain,
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
    | ~ spl6_44 ),
    inference(resolution,[],[f385,f68])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f385,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl6_44
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f201,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_21
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f995,plain,
    ( ~ spl6_23
    | spl6_90
    | ~ spl6_92
    | ~ spl6_96 ),
    inference(avatar_contradiction_clause,[],[f994])).

fof(f994,plain,
    ( $false
    | ~ spl6_23
    | spl6_90
    | ~ spl6_92
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f993,f897])).

fof(f897,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | spl6_90 ),
    inference(avatar_component_clause,[],[f896])).

fof(f896,plain,
    ( spl6_90
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f988,plain,
    ( spl6_96
    | ~ spl6_94 ),
    inference(avatar_split_clause,[],[f955,f948,f986])).

fof(f948,plain,
    ( spl6_94
  <=> r1_xboole_0(k1_relat_1(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f955,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK4),sK3)
    | ~ spl6_94 ),
    inference(resolution,[],[f949,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f949,plain,
    ( r1_xboole_0(k1_relat_1(sK4),sK3)
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f948])).

fof(f950,plain,
    ( spl6_94
    | ~ spl6_23
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f941,f924,f207,f948])).

fof(f941,plain,
    ( r1_xboole_0(k1_relat_1(sK4),sK3)
    | ~ spl6_23
    | ~ spl6_92 ),
    inference(trivial_inequality_removal,[],[f940])).

fof(f940,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK4),sK3)
    | ~ spl6_23
    | ~ spl6_92 ),
    inference(superposition,[],[f210,f925])).

fof(f210,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k7_relat_1(sK4,X0)
        | r1_xboole_0(k1_relat_1(sK4),X0) )
    | ~ spl6_23 ),
    inference(resolution,[],[f208,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f926,plain,
    ( spl6_92
    | ~ spl6_8
    | ~ spl6_50
    | ~ spl6_55 ),
    inference(avatar_split_clause,[],[f921,f724,f618,f101,f924])).

fof(f101,plain,
    ( spl6_8
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f618,plain,
    ( spl6_50
  <=> v1_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f724,plain,
    ( spl6_55
  <=> sK4 = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f921,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_8
    | ~ spl6_50
    | ~ spl6_55 ),
    inference(forward_demodulation,[],[f918,f725])).

fof(f725,plain,
    ( sK4 = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f724])).

fof(f918,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2),sK3)
    | ~ spl6_8
    | ~ spl6_50 ),
    inference(resolution,[],[f629,f102])).

fof(f102,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f629,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),X2),X3) )
    | ~ spl6_50 ),
    inference(resolution,[],[f619,f58])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f619,plain,
    ( v1_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f618])).

fof(f898,plain,
    ( ~ spl6_90
    | spl6_47
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f846,f833,f563,f896])).

fof(f563,plain,
    ( spl6_47
  <=> k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f846,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | spl6_47
    | ~ spl6_78 ),
    inference(superposition,[],[f564,f834])).

fof(f564,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl6_47 ),
    inference(avatar_component_clause,[],[f563])).

fof(f835,plain,
    ( spl6_78
    | ~ spl6_19
    | ~ spl6_59
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f831,f815,f739,f183,f833])).

fof(f183,plain,
    ( spl6_19
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f739,plain,
    ( spl6_59
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f815,plain,
    ( spl6_74
  <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f831,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_19
    | ~ spl6_59
    | ~ spl6_74 ),
    inference(forward_demodulation,[],[f828,f740])).

fof(f740,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f739])).

fof(f828,plain,
    ( k7_relat_1(sK5,sK2) = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_19
    | ~ spl6_74 ),
    inference(superposition,[],[f194,f816])).

fof(f816,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK5),sK2)
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f815])).

fof(f194,plain,
    ( ! [X1] : k7_relat_1(sK5,X1) = k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X1))
    | ~ spl6_19 ),
    inference(resolution,[],[f184,f61])).

fof(f184,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f183])).

fof(f817,plain,
    ( spl6_74
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f789,f771,f815])).

fof(f771,plain,
    ( spl6_66
  <=> r1_xboole_0(k1_relat_1(sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f789,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_relat_1(sK5),sK2)
    | ~ spl6_66 ),
    inference(resolution,[],[f772,f60])).

fof(f772,plain,
    ( r1_xboole_0(k1_relat_1(sK5),sK2)
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f771])).

fof(f773,plain,
    ( spl6_66
    | ~ spl6_19
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f767,f739,f183,f771])).

fof(f767,plain,
    ( r1_xboole_0(k1_relat_1(sK5),sK2)
    | ~ spl6_19
    | ~ spl6_59 ),
    inference(trivial_inequality_removal,[],[f766])).

fof(f766,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK5),sK2)
    | ~ spl6_19
    | ~ spl6_59 ),
    inference(superposition,[],[f193,f740])).

fof(f193,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k7_relat_1(sK5,X0)
        | r1_xboole_0(k1_relat_1(sK5),X0) )
    | ~ spl6_19 ),
    inference(resolution,[],[f184,f64])).

fof(f752,plain,
    ( spl6_59
    | ~ spl6_53
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f741,f732,f663,f739])).

fof(f663,plain,
    ( spl6_53
  <=> sK5 = k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f732,plain,
    ( spl6_57
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f741,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_53
    | ~ spl6_57 ),
    inference(forward_demodulation,[],[f733,f664])).

fof(f664,plain,
    ( sK5 = k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f663])).

fof(f733,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3),sK2)
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f732])).

fof(f734,plain,
    ( spl6_57
    | ~ spl6_11
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f643,f495,f116,f732])).

fof(f116,plain,
    ( spl6_11
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f495,plain,
    ( spl6_46
  <=> v1_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f643,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3),sK2)
    | ~ spl6_11
    | ~ spl6_46 ),
    inference(resolution,[],[f612,f117])).

fof(f117,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f612,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(X2,X3)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),X2),X3) )
    | ~ spl6_46 ),
    inference(resolution,[],[f496,f58])).

fof(f496,plain,
    ( v1_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f495])).

fof(f726,plain,
    ( spl6_55
    | ~ spl6_37
    | ~ spl6_45
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f705,f637,f388,f354,f724])).

fof(f354,plain,
    ( spl6_37
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f388,plain,
    ( spl6_45
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f637,plain,
    ( spl6_52
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f705,plain,
    ( sK4 = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_37
    | ~ spl6_45
    | ~ spl6_52 ),
    inference(superposition,[],[f605,f638])).

fof(f638,plain,
    ( sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f637])).

fof(f605,plain,
    ( ! [X0] : k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),X0)
    | ~ spl6_37
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f575,f355])).

fof(f355,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f354])).

fof(f575,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),X0) )
    | ~ spl6_45 ),
    inference(resolution,[],[f389,f53])).

fof(f389,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1)))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f388])).

fof(f665,plain,
    ( spl6_53
    | ~ spl6_34
    | ~ spl6_42
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f644,f633,f376,f322,f663])).

fof(f322,plain,
    ( spl6_34
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f376,plain,
    ( spl6_42
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f633,plain,
    ( spl6_51
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f644,plain,
    ( sK5 = k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_34
    | ~ spl6_42
    | ~ spl6_51 ),
    inference(superposition,[],[f430,f634])).

fof(f634,plain,
    ( sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f633])).

fof(f430,plain,
    ( ! [X0] : k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),X0)
    | ~ spl6_34
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f400,f323])).

fof(f323,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f322])).

fof(f400,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
        | k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),X0) )
    | ~ spl6_42 ),
    inference(resolution,[],[f377,f53])).

fof(f377,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1)))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f376])).

fof(f639,plain,
    ( spl6_52
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f592,f388,f372,f354,f168,f129,f112,f90,f86,f82,f74,f637])).

fof(f372,plain,
    ( spl6_41
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f592,plain,
    ( sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f591,f91])).

fof(f591,plain,
    ( v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f590,f373])).

fof(f373,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f372])).

fof(f590,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_37
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f589,f355])).

fof(f589,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f588,f169])).

fof(f588,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f587,f113])).

fof(f587,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | ~ spl6_13
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f586,f75])).

fof(f586,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | spl6_4
    | spl6_5
    | ~ spl6_13
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f585,f130])).

fof(f585,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | spl6_4
    | spl6_5
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f584,f83])).

fof(f584,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | spl6_5
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f583,f87])).

fof(f583,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_45 ),
    inference(trivial_inequality_removal,[],[f582])).

fof(f582,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK2)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK2))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_45 ),
    inference(duplicate_literal_removal,[],[f566])).

fof(f566,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK2)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK2))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)
    | ~ spl6_45 ),
    inference(resolution,[],[f389,f68])).

fof(f635,plain,
    ( spl6_51
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f417,f376,f360,f322,f162,f120,f105,f90,f86,f78,f70,f633])).

fof(f360,plain,
    ( spl6_38
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f417,plain,
    ( sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f416,f91])).

fof(f416,plain,
    ( v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_34
    | ~ spl6_38
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f415,f361])).

fof(f361,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f360])).

fof(f415,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_34
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f414,f323])).

fof(f414,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f413,f163])).

fof(f413,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f412,f106])).

fof(f412,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | ~ spl6_12
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f411,f71])).

fof(f411,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | spl6_3
    | spl6_5
    | ~ spl6_12
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f410,f121])).

fof(f410,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | spl6_3
    | spl6_5
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f409,f79])).

fof(f409,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | spl6_5
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f408,f87])).

fof(f408,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_42 ),
    inference(trivial_inequality_removal,[],[f407])).

fof(f407,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK3,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK3,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_42 ),
    inference(duplicate_literal_removal,[],[f391])).

fof(f391,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK3,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK3,sK3))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)
    | ~ spl6_42 ),
    inference(resolution,[],[f377,f68])).

fof(f620,plain,
    ( spl6_50
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f574,f388,f618])).

fof(f574,plain,
    ( v1_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ spl6_45 ),
    inference(resolution,[],[f389,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f565,plain,
    ( ~ spl6_47
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f548,f384,f368,f350,f197,f168,f162,f158,f129,f120,f112,f105,f90,f86,f82,f78,f74,f70,f563])).

fof(f197,plain,
    ( spl6_20
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f548,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f547,f192])).

fof(f547,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f546,f159])).

fof(f546,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f545,f137])).

fof(f545,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f544,f181])).

fof(f544,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f543,f198])).

fof(f198,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f543,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f542,f91])).

fof(f542,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_36
    | ~ spl6_40
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f541,f369])).

fof(f541,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_36
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f540,f351])).

fof(f540,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f539,f163])).

fof(f539,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f538,f106])).

fof(f538,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f537,f71])).

fof(f537,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_17
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f536,f169])).

fof(f536,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f535,f113])).

fof(f535,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f534,f75])).

fof(f534,plain,
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
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f533,f121])).

fof(f533,plain,
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
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f532,f79])).

fof(f532,plain,
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
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f531,f130])).

fof(f531,plain,
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
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f530,f83])).

fof(f530,plain,
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
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f499,f87])).

fof(f499,plain,
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
    | ~ spl6_44 ),
    inference(resolution,[],[f385,f67])).

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

fof(f497,plain,
    ( spl6_46
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f399,f376,f495])).

fof(f399,plain,
    ( v1_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ spl6_42 ),
    inference(resolution,[],[f377,f55])).

fof(f390,plain,
    ( spl6_45
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f348,f168,f129,f112,f90,f86,f82,f74,f388])).

fof(f348,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1)))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f347,f83])).

fof(f347,plain,
    ( v1_xboole_0(sK2)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1)))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f346,f113])).

fof(f346,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_xboole_0(sK2)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1)))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f345,f75])).

fof(f345,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_xboole_0(sK2)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1)))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f340,f130])).

fof(f340,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_xboole_0(sK2)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1)))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(resolution,[],[f249,f169])).

fof(f249,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f248,f87])).

fof(f248,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f247,f113])).

fof(f247,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f246,f75])).

fof(f246,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(resolution,[],[f156,f169])).

fof(f156,plain,
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
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f155,f91])).

fof(f155,plain,
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
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f150,f83])).

fof(f150,plain,
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
    | ~ spl6_13 ),
    inference(resolution,[],[f130,f49])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f386,plain,
    ( spl6_44
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f344,f168,f162,f129,f120,f112,f105,f90,f86,f82,f78,f74,f70,f384])).

fof(f344,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f343,f79])).

fof(f343,plain,
    ( v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f342,f106])).

fof(f342,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f341,f71])).

fof(f341,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f339,f121])).

fof(f339,plain,
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
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(resolution,[],[f249,f163])).

fof(f378,plain,
    ( spl6_42
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f330,f162,f120,f105,f90,f86,f78,f70,f376])).

fof(f330,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1)))
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f329,f79])).

fof(f329,plain,
    ( v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1)))
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f328,f106])).

fof(f328,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1)))
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f327,f71])).

fof(f327,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1)))
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f325,f121])).

fof(f325,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1)))
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(resolution,[],[f245,f163])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | v1_xboole_0(X0)
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X0),sK1))) )
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f244,f87])).

fof(f244,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X0),sK1))) )
    | ~ spl6_1
    | spl6_3
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f243,f106])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_2(sK5,sK3,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X0),sK1))) )
    | ~ spl6_1
    | spl6_3
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f242,f71])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X0),sK1))) )
    | spl6_3
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(resolution,[],[f146,f163])).

fof(f146,plain,
    ( ! [X12,X10,X11,X9] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK3,X9)))
        | v1_xboole_0(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,sK3,X9)
        | v1_xboole_0(X9)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X9)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9)))
        | m1_subset_1(k1_tmap_1(sK0,X9,sK3,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X10),X9))) )
    | spl6_3
    | spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f145,f91])).

fof(f145,plain,
    ( ! [X12,X10,X11,X9] :
        ( v1_xboole_0(X9)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,sK3,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK3,X9)))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X9)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9)))
        | m1_subset_1(k1_tmap_1(sK0,X9,sK3,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X10),X9))) )
    | spl6_3
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f140,f79])).

fof(f140,plain,
    ( ! [X12,X10,X11,X9] :
        ( v1_xboole_0(X9)
        | v1_xboole_0(sK3)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,sK3,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK3,X9)))
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X9)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9)))
        | m1_subset_1(k1_tmap_1(sK0,X9,sK3,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X10),X9))) )
    | ~ spl6_12 ),
    inference(resolution,[],[f121,f49])).

fof(f374,plain,
    ( spl6_41
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f320,f168,f129,f112,f90,f86,f82,f74,f372])).

fof(f320,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f319,f83])).

fof(f319,plain,
    ( v1_xboole_0(sK2)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f318,f113])).

fof(f318,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_xboole_0(sK2)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f317,f75])).

fof(f317,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_xboole_0(sK2)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f312,f130])).

fof(f312,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_xboole_0(sK2)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(resolution,[],[f241,f169])).

fof(f241,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f240,f87])).

fof(f240,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f239,f113])).

fof(f239,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f238,f75])).

fof(f238,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(resolution,[],[f154,f169])).

fof(f154,plain,
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
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f153,f91])).

fof(f153,plain,
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
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f149,f83])).

fof(f149,plain,
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
    | ~ spl6_13 ),
    inference(resolution,[],[f130,f48])).

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

fof(f370,plain,
    ( spl6_40
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f316,f168,f162,f129,f120,f112,f105,f90,f86,f82,f78,f74,f70,f368])).

fof(f316,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f315,f79])).

fof(f315,plain,
    ( v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f314,f106])).

fof(f314,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f313,f71])).

fof(f313,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f311,f121])).

fof(f311,plain,
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
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(resolution,[],[f241,f163])).

fof(f362,plain,
    ( spl6_38
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f306,f162,f120,f105,f90,f86,f78,f70,f360])).

fof(f306,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f305,f79])).

fof(f305,plain,
    ( v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f304,f106])).

fof(f304,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f303,f71])).

fof(f303,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f301,f121])).

fof(f301,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(resolution,[],[f233,f163])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | v1_xboole_0(X0)
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k4_subset_1(sK0,sK3,X0),sK1) )
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
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
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k4_subset_1(sK0,sK3,X0),sK1) )
    | ~ spl6_1
    | spl6_3
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f231,f106])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_2(sK5,sK3,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k4_subset_1(sK0,sK3,X0),sK1) )
    | ~ spl6_1
    | spl6_3
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f230,f71])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k4_subset_1(sK0,sK3,X0),sK1) )
    | spl6_3
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(resolution,[],[f144,f163])).

fof(f144,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,X5)))
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,sK3,X5)
        | v1_xboole_0(X5)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X5)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
        | v1_funct_2(k1_tmap_1(sK0,X5,sK3,X6,X7,X8),k4_subset_1(sK0,sK3,X6),X5) )
    | spl6_3
    | spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f143,f91])).

fof(f143,plain,
    ( ! [X6,X8,X7,X5] :
        ( v1_xboole_0(X5)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,sK3,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,X5)))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X5)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
        | v1_funct_2(k1_tmap_1(sK0,X5,sK3,X6,X7,X8),k4_subset_1(sK0,sK3,X6),X5) )
    | spl6_3
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f139,f79])).

fof(f139,plain,
    ( ! [X6,X8,X7,X5] :
        ( v1_xboole_0(X5)
        | v1_xboole_0(sK3)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,sK3,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,X5)))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,X6,X5)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
        | v1_funct_2(k1_tmap_1(sK0,X5,sK3,X6,X7,X8),k4_subset_1(sK0,sK3,X6),X5) )
    | ~ spl6_12 ),
    inference(resolution,[],[f121,f48])).

fof(f356,plain,
    ( spl6_37
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f300,f168,f129,f112,f90,f86,f82,f74,f354])).

fof(f300,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f299,f83])).

fof(f299,plain,
    ( v1_xboole_0(sK2)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f298,f113])).

fof(f298,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_xboole_0(sK2)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f297,f75])).

fof(f297,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_xboole_0(sK2)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f292,f130])).

fof(f292,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_xboole_0(sK2)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(resolution,[],[f225,f169])).

fof(f225,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f224,f87])).

fof(f224,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f223,f113])).

fof(f223,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f222,f75])).

fof(f222,plain,
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
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(resolution,[],[f152,f169])).

fof(f152,plain,
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
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f151,f91])).

fof(f151,plain,
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
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f148,f83])).

fof(f148,plain,
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
    | ~ spl6_13 ),
    inference(resolution,[],[f130,f47])).

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

fof(f352,plain,
    ( spl6_36
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f296,f168,f162,f129,f120,f112,f105,f90,f86,f82,f78,f74,f70,f350])).

fof(f296,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f295,f79])).

fof(f295,plain,
    ( v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f294,f106])).

fof(f294,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f293,f71])).

fof(f293,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f291,f121])).

fof(f291,plain,
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
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_17 ),
    inference(resolution,[],[f225,f163])).

fof(f324,plain,
    ( spl6_34
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f282,f162,f120,f105,f90,f86,f78,f70,f322])).

fof(f282,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f281,f79])).

fof(f281,plain,
    ( v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f280,f106])).

fof(f280,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f279,f71])).

fof(f279,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f277,f121])).

fof(f277,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(resolution,[],[f219,f163])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | v1_xboole_0(X0)
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1)) )
    | ~ spl6_1
    | spl6_3
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f218,f87])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1)) )
    | ~ spl6_1
    | spl6_3
    | spl6_6
    | ~ spl6_9
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f217,f106])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_2(sK5,sK3,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1)) )
    | ~ spl6_1
    | spl6_3
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f216,f71])).

fof(f216,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(sK5)
        | ~ v1_funct_2(sK5,sK3,sK1)
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1)) )
    | spl6_3
    | spl6_6
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(resolution,[],[f142,f163])).

fof(f142,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,sK3,X1)
        | v1_xboole_0(X1)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,X2,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | v1_funct_1(k1_tmap_1(sK0,X1,sK3,X2,X3,X4)) )
    | spl6_3
    | spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f141,f91])).

fof(f141,plain,
    ( ! [X4,X2,X3,X1] :
        ( v1_xboole_0(X1)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,sK3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,X2,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | v1_funct_1(k1_tmap_1(sK0,X1,sK3,X2,X3,X4)) )
    | spl6_3
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f138,f79])).

fof(f138,plain,
    ( ! [X4,X2,X3,X1] :
        ( v1_xboole_0(X1)
        | v1_xboole_0(sK3)
        | v1_xboole_0(sK0)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,sK3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,X2,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | v1_funct_1(k1_tmap_1(sK0,X1,sK3,X2,X3,X4)) )
    | ~ spl6_12 ),
    inference(resolution,[],[f121,f47])).

fof(f209,plain,
    ( spl6_23
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f186,f168,f207])).

fof(f186,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_17 ),
    inference(resolution,[],[f169,f55])).

fof(f205,plain,
    ( ~ spl6_20
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f33,f203,f200,f197])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f185,plain,
    ( spl6_19
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f175,f162,f183])).

fof(f175,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_16 ),
    inference(resolution,[],[f163,f55])).

fof(f170,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f39,f168])).

fof(f39,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f164,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f36,f162])).

fof(f36,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f160,plain,
    ( spl6_15
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f109,f101,f158])).

fof(f109,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl6_8 ),
    inference(resolution,[],[f102,f60])).

fof(f131,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f44,f129])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f122,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f41,f120])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f118,plain,
    ( spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f108,f101,f116])).

fof(f108,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f102,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f114,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f38,f112])).

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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:23:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (5796)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (5788)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (5780)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (5789)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (5782)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (5793)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (5784)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (5790)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (5794)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (5791)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (5781)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (5786)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (5799)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (5787)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (5800)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (5800)Refutation not found, incomplete strategy% (5800)------------------------------
% 0.21/0.51  % (5800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5800)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5800)Memory used [KB]: 10618
% 0.21/0.51  % (5800)Time elapsed: 0.105 s
% 0.21/0.51  % (5800)------------------------------
% 0.21/0.51  % (5800)------------------------------
% 0.21/0.51  % (5792)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (5783)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (5797)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (5785)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (5780)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f1020,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f96,f103,f107,f114,f118,f122,f131,f160,f164,f170,f185,f205,f209,f324,f352,f356,f362,f370,f374,f378,f386,f390,f497,f565,f620,f635,f639,f665,f726,f734,f752,f773,f817,f835,f898,f926,f950,f988,f995,f1011,f1019])).
% 0.21/0.52  fof(f1019,plain,(
% 0.21/0.52    ~spl6_1 | ~spl6_2 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_22 | ~spl6_23 | ~spl6_78 | ~spl6_92 | ~spl6_96),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1018])).
% 0.21/0.52  fof(f1018,plain,(
% 0.21/0.52    $false | (~spl6_1 | ~spl6_2 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_22 | ~spl6_23 | ~spl6_78 | ~spl6_92 | ~spl6_96)),
% 0.21/0.52    inference(subsumption_resolution,[],[f1017,f993])).
% 0.21/0.52  fof(f993,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl6_23 | ~spl6_92 | ~spl6_96)),
% 0.21/0.52    inference(forward_demodulation,[],[f990,f925])).
% 0.21/0.52  fof(f925,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK4,sK3) | ~spl6_92),
% 0.21/0.52    inference(avatar_component_clause,[],[f924])).
% 0.21/0.52  fof(f924,plain,(
% 0.21/0.52    spl6_92 <=> k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 0.21/0.52  fof(f990,plain,(
% 0.21/0.52    k7_relat_1(sK4,sK3) = k7_relat_1(sK4,k1_xboole_0) | (~spl6_23 | ~spl6_96)),
% 0.21/0.52    inference(superposition,[],[f211,f987])).
% 0.21/0.52  fof(f987,plain,(
% 0.21/0.52    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK4),sK3) | ~spl6_96),
% 0.21/0.52    inference(avatar_component_clause,[],[f986])).
% 0.21/0.52  fof(f986,plain,(
% 0.21/0.52    spl6_96 <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK4),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    ( ! [X1] : (k7_relat_1(sK4,X1) = k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X1))) ) | ~spl6_23),
% 0.21/0.52    inference(resolution,[],[f208,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    v1_relat_1(sK4) | ~spl6_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f207])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    spl6_23 <=> v1_relat_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.52  fof(f1017,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (~spl6_1 | ~spl6_2 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_22 | ~spl6_78)),
% 0.21/0.52    inference(forward_demodulation,[],[f1016,f834])).
% 0.21/0.52  fof(f834,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl6_78),
% 0.21/0.52    inference(avatar_component_clause,[],[f833])).
% 0.21/0.52  fof(f833,plain,(
% 0.21/0.52    spl6_78 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 0.21/0.52  fof(f1016,plain,(
% 0.21/0.52    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (~spl6_1 | ~spl6_2 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_22)),
% 0.21/0.52    inference(forward_demodulation,[],[f1015,f192])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) ) | (~spl6_2 | ~spl6_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f187,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    v1_funct_1(sK4) | ~spl6_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl6_2 <=> v1_funct_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_1(sK4) | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) ) | ~spl6_17),
% 0.21/0.52    inference(resolution,[],[f169,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    spl6_17 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.52  fof(f1015,plain,(
% 0.21/0.52    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl6_1 | ~spl6_12 | ~spl6_15 | ~spl6_16 | spl6_22)),
% 0.21/0.52    inference(forward_demodulation,[],[f1014,f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl6_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f158])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    spl6_15 <=> k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.52  fof(f1014,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_12 | ~spl6_16 | spl6_22)),
% 0.21/0.52    inference(forward_demodulation,[],[f1013,f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)) ) | ~spl6_12),
% 0.21/0.52    inference(resolution,[],[f121,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    spl6_12 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.52  fof(f1013,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_16 | spl6_22)),
% 0.21/0.52    inference(forward_demodulation,[],[f204,f181])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    ( ! [X0] : (k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)) ) | (~spl6_1 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f176,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    v1_funct_1(sK5) | ~spl6_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl6_1 <=> v1_funct_1(sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_1(sK5) | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)) ) | ~spl6_16),
% 0.21/0.52    inference(resolution,[],[f163,f53])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl6_16 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f203])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    spl6_22 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.52  fof(f1011,plain,(
% 0.21/0.52    ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_21 | ~spl6_23 | ~spl6_36 | ~spl6_40 | ~spl6_44 | ~spl6_78 | ~spl6_92 | ~spl6_96),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1010])).
% 0.21/0.52  fof(f1010,plain,(
% 0.21/0.52    $false | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_21 | ~spl6_23 | ~spl6_36 | ~spl6_40 | ~spl6_44 | ~spl6_78 | ~spl6_92 | ~spl6_96)),
% 0.21/0.52    inference(subsumption_resolution,[],[f201,f1009])).
% 0.21/0.52  fof(f1009,plain,(
% 0.21/0.52    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_23 | ~spl6_36 | ~spl6_40 | ~spl6_44 | ~spl6_78 | ~spl6_92 | ~spl6_96)),
% 0.21/0.52    inference(subsumption_resolution,[],[f998,f993])).
% 0.21/0.52  fof(f998,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_36 | ~spl6_40 | ~spl6_44 | ~spl6_78)),
% 0.21/0.52    inference(forward_demodulation,[],[f529,f834])).
% 0.21/0.52  fof(f529,plain,(
% 0.21/0.52    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.52    inference(forward_demodulation,[],[f528,f192])).
% 0.21/0.52  fof(f528,plain,(
% 0.21/0.52    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.52    inference(forward_demodulation,[],[f527,f159])).
% 0.21/0.52  fof(f527,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.52    inference(forward_demodulation,[],[f526,f137])).
% 0.21/0.52  fof(f526,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.52    inference(forward_demodulation,[],[f525,f181])).
% 0.21/0.52  fof(f525,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f524,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ~v1_xboole_0(sK0) | spl6_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl6_6 <=> v1_xboole_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.52  fof(f524,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f523,f369])).
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~spl6_40),
% 0.21/0.52    inference(avatar_component_clause,[],[f368])).
% 0.21/0.52  fof(f368,plain,(
% 0.21/0.52    spl6_40 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.21/0.52  fof(f523,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | ~spl6_36 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f522,f351])).
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_36),
% 0.21/0.52    inference(avatar_component_clause,[],[f350])).
% 0.21/0.52  fof(f350,plain,(
% 0.21/0.52    spl6_36 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.52  fof(f522,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f521,f163])).
% 0.21/0.52  fof(f521,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f520,f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    v1_funct_2(sK5,sK3,sK1) | ~spl6_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl6_9 <=> v1_funct_2(sK5,sK3,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.52  fof(f520,plain,(
% 0.21/0.52    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f519,f71])).
% 0.21/0.52  % (5798)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  fof(f519,plain,(
% 0.21/0.52    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f518,f169])).
% 0.21/0.52  fof(f518,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f517,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    v1_funct_2(sK4,sK2,sK1) | ~spl6_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    spl6_10 <=> v1_funct_2(sK4,sK2,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.52  fof(f517,plain,(
% 0.21/0.52    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_13 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f516,f75])).
% 0.21/0.52  fof(f516,plain,(
% 0.21/0.52    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_13 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f515,f121])).
% 0.21/0.52  fof(f515,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_13 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f514,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ~v1_xboole_0(sK3) | spl6_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl6_3 <=> v1_xboole_0(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f514,plain,(
% 0.21/0.52    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_4 | spl6_5 | ~spl6_13 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f513,f130])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl6_13 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.52  fof(f513,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_4 | spl6_5 | ~spl6_44)),
% 0.21/0.52    inference(subsumption_resolution,[],[f512,f83])).
% 0.21/0.52  % (5781)Refutation not found, incomplete strategy% (5781)------------------------------
% 0.21/0.52  % (5781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5781)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5781)Memory used [KB]: 10746
% 0.21/0.52  % (5781)Time elapsed: 0.112 s
% 0.21/0.52  % (5781)------------------------------
% 0.21/0.52  % (5781)------------------------------
% 0.21/0.53  % (5795)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ~v1_xboole_0(sK2) | spl6_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl6_4 <=> v1_xboole_0(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.53  fof(f512,plain,(
% 0.21/0.53    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_5 | ~spl6_44)),
% 0.21/0.53    inference(subsumption_resolution,[],[f498,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ~v1_xboole_0(sK1) | spl6_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl6_5 <=> v1_xboole_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.53  fof(f498,plain,(
% 0.21/0.53    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl6_44),
% 0.21/0.53    inference(resolution,[],[f385,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.21/0.53    inference(equality_resolution,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.21/0.53  fof(f385,plain,(
% 0.21/0.53    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl6_44),
% 0.21/0.53    inference(avatar_component_clause,[],[f384])).
% 0.21/0.53  fof(f384,plain,(
% 0.21/0.53    spl6_44 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl6_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f200])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    spl6_21 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.53  fof(f995,plain,(
% 0.21/0.53    ~spl6_23 | spl6_90 | ~spl6_92 | ~spl6_96),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f994])).
% 0.21/0.53  fof(f994,plain,(
% 0.21/0.53    $false | (~spl6_23 | spl6_90 | ~spl6_92 | ~spl6_96)),
% 0.21/0.53    inference(subsumption_resolution,[],[f993,f897])).
% 0.21/0.53  fof(f897,plain,(
% 0.21/0.53    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | spl6_90),
% 0.21/0.53    inference(avatar_component_clause,[],[f896])).
% 0.21/0.53  fof(f896,plain,(
% 0.21/0.53    spl6_90 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).
% 0.21/0.53  fof(f988,plain,(
% 0.21/0.53    spl6_96 | ~spl6_94),
% 0.21/0.53    inference(avatar_split_clause,[],[f955,f948,f986])).
% 0.21/0.53  fof(f948,plain,(
% 0.21/0.53    spl6_94 <=> r1_xboole_0(k1_relat_1(sK4),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 0.21/0.53  fof(f955,plain,(
% 0.21/0.53    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK4),sK3) | ~spl6_94),
% 0.21/0.53    inference(resolution,[],[f949,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.53  fof(f949,plain,(
% 0.21/0.53    r1_xboole_0(k1_relat_1(sK4),sK3) | ~spl6_94),
% 0.21/0.53    inference(avatar_component_clause,[],[f948])).
% 0.21/0.53  fof(f950,plain,(
% 0.21/0.53    spl6_94 | ~spl6_23 | ~spl6_92),
% 0.21/0.53    inference(avatar_split_clause,[],[f941,f924,f207,f948])).
% 0.21/0.53  fof(f941,plain,(
% 0.21/0.53    r1_xboole_0(k1_relat_1(sK4),sK3) | (~spl6_23 | ~spl6_92)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f940])).
% 0.21/0.53  fof(f940,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK4),sK3) | (~spl6_23 | ~spl6_92)),
% 0.21/0.53    inference(superposition,[],[f210,f925])).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k7_relat_1(sK4,X0) | r1_xboole_0(k1_relat_1(sK4),X0)) ) | ~spl6_23),
% 0.21/0.53    inference(resolution,[],[f208,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.53  fof(f926,plain,(
% 0.21/0.53    spl6_92 | ~spl6_8 | ~spl6_50 | ~spl6_55),
% 0.21/0.53    inference(avatar_split_clause,[],[f921,f724,f618,f101,f924])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl6_8 <=> r1_xboole_0(sK2,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.53  fof(f618,plain,(
% 0.21/0.53    spl6_50 <=> v1_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 0.21/0.53  fof(f724,plain,(
% 0.21/0.53    spl6_55 <=> sK4 = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 0.21/0.53  fof(f921,plain,(
% 0.21/0.53    k1_xboole_0 = k7_relat_1(sK4,sK3) | (~spl6_8 | ~spl6_50 | ~spl6_55)),
% 0.21/0.53    inference(forward_demodulation,[],[f918,f725])).
% 0.21/0.53  fof(f725,plain,(
% 0.21/0.53    sK4 = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | ~spl6_55),
% 0.21/0.53    inference(avatar_component_clause,[],[f724])).
% 0.21/0.53  fof(f918,plain,(
% 0.21/0.53    k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2),sK3) | (~spl6_8 | ~spl6_50)),
% 0.21/0.53    inference(resolution,[],[f629,f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    r1_xboole_0(sK2,sK3) | ~spl6_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f101])).
% 0.21/0.53  fof(f629,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),X2),X3)) ) | ~spl6_50),
% 0.21/0.53    inference(resolution,[],[f619,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.21/0.53  fof(f619,plain,(
% 0.21/0.53    v1_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~spl6_50),
% 0.21/0.53    inference(avatar_component_clause,[],[f618])).
% 0.21/0.53  fof(f898,plain,(
% 0.21/0.53    ~spl6_90 | spl6_47 | ~spl6_78),
% 0.21/0.53    inference(avatar_split_clause,[],[f846,f833,f563,f896])).
% 0.21/0.53  fof(f563,plain,(
% 0.21/0.53    spl6_47 <=> k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 0.21/0.53  fof(f846,plain,(
% 0.21/0.53    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | (spl6_47 | ~spl6_78)),
% 0.21/0.53    inference(superposition,[],[f564,f834])).
% 0.21/0.53  fof(f564,plain,(
% 0.21/0.53    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | spl6_47),
% 0.21/0.53    inference(avatar_component_clause,[],[f563])).
% 0.21/0.53  fof(f835,plain,(
% 0.21/0.53    spl6_78 | ~spl6_19 | ~spl6_59 | ~spl6_74),
% 0.21/0.53    inference(avatar_split_clause,[],[f831,f815,f739,f183,f833])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    spl6_19 <=> v1_relat_1(sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.53  fof(f739,plain,(
% 0.21/0.53    spl6_59 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.21/0.53  fof(f815,plain,(
% 0.21/0.53    spl6_74 <=> k1_xboole_0 = k3_xboole_0(k1_relat_1(sK5),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 0.21/0.53  fof(f831,plain,(
% 0.21/0.53    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl6_19 | ~spl6_59 | ~spl6_74)),
% 0.21/0.53    inference(forward_demodulation,[],[f828,f740])).
% 0.21/0.53  fof(f740,plain,(
% 0.21/0.53    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl6_59),
% 0.21/0.53    inference(avatar_component_clause,[],[f739])).
% 0.21/0.53  fof(f828,plain,(
% 0.21/0.53    k7_relat_1(sK5,sK2) = k7_relat_1(sK5,k1_xboole_0) | (~spl6_19 | ~spl6_74)),
% 0.21/0.53    inference(superposition,[],[f194,f816])).
% 0.21/0.53  fof(f816,plain,(
% 0.21/0.53    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK5),sK2) | ~spl6_74),
% 0.21/0.53    inference(avatar_component_clause,[],[f815])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ( ! [X1] : (k7_relat_1(sK5,X1) = k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X1))) ) | ~spl6_19),
% 0.21/0.53    inference(resolution,[],[f184,f61])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    v1_relat_1(sK5) | ~spl6_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f183])).
% 0.21/0.53  fof(f817,plain,(
% 0.21/0.53    spl6_74 | ~spl6_66),
% 0.21/0.53    inference(avatar_split_clause,[],[f789,f771,f815])).
% 0.21/0.53  fof(f771,plain,(
% 0.21/0.53    spl6_66 <=> r1_xboole_0(k1_relat_1(sK5),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 0.21/0.53  fof(f789,plain,(
% 0.21/0.53    k1_xboole_0 = k3_xboole_0(k1_relat_1(sK5),sK2) | ~spl6_66),
% 0.21/0.53    inference(resolution,[],[f772,f60])).
% 0.21/0.53  fof(f772,plain,(
% 0.21/0.53    r1_xboole_0(k1_relat_1(sK5),sK2) | ~spl6_66),
% 0.21/0.53    inference(avatar_component_clause,[],[f771])).
% 0.21/0.53  fof(f773,plain,(
% 0.21/0.53    spl6_66 | ~spl6_19 | ~spl6_59),
% 0.21/0.53    inference(avatar_split_clause,[],[f767,f739,f183,f771])).
% 0.21/0.53  fof(f767,plain,(
% 0.21/0.53    r1_xboole_0(k1_relat_1(sK5),sK2) | (~spl6_19 | ~spl6_59)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f766])).
% 0.21/0.53  fof(f766,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK5),sK2) | (~spl6_19 | ~spl6_59)),
% 0.21/0.53    inference(superposition,[],[f193,f740])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k7_relat_1(sK5,X0) | r1_xboole_0(k1_relat_1(sK5),X0)) ) | ~spl6_19),
% 0.21/0.53    inference(resolution,[],[f184,f64])).
% 0.21/0.53  fof(f752,plain,(
% 0.21/0.53    spl6_59 | ~spl6_53 | ~spl6_57),
% 0.21/0.53    inference(avatar_split_clause,[],[f741,f732,f663,f739])).
% 0.21/0.53  fof(f663,plain,(
% 0.21/0.53    spl6_53 <=> sK5 = k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.21/0.53  fof(f732,plain,(
% 0.21/0.53    spl6_57 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 0.21/0.53  fof(f741,plain,(
% 0.21/0.53    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl6_53 | ~spl6_57)),
% 0.21/0.53    inference(forward_demodulation,[],[f733,f664])).
% 0.21/0.53  fof(f664,plain,(
% 0.21/0.53    sK5 = k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | ~spl6_53),
% 0.21/0.53    inference(avatar_component_clause,[],[f663])).
% 0.21/0.53  fof(f733,plain,(
% 0.21/0.53    k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3),sK2) | ~spl6_57),
% 0.21/0.53    inference(avatar_component_clause,[],[f732])).
% 0.21/0.53  fof(f734,plain,(
% 0.21/0.53    spl6_57 | ~spl6_11 | ~spl6_46),
% 0.21/0.53    inference(avatar_split_clause,[],[f643,f495,f116,f732])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl6_11 <=> r1_xboole_0(sK3,sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.53  fof(f495,plain,(
% 0.21/0.53    spl6_46 <=> v1_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.21/0.53  fof(f643,plain,(
% 0.21/0.53    k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3),sK2) | (~spl6_11 | ~spl6_46)),
% 0.21/0.53    inference(resolution,[],[f612,f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    r1_xboole_0(sK3,sK2) | ~spl6_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f116])).
% 0.21/0.53  fof(f612,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | k1_xboole_0 = k7_relat_1(k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),X2),X3)) ) | ~spl6_46),
% 0.21/0.53    inference(resolution,[],[f496,f58])).
% 0.21/0.53  fof(f496,plain,(
% 0.21/0.53    v1_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~spl6_46),
% 0.21/0.53    inference(avatar_component_clause,[],[f495])).
% 0.21/0.53  fof(f726,plain,(
% 0.21/0.53    spl6_55 | ~spl6_37 | ~spl6_45 | ~spl6_52),
% 0.21/0.53    inference(avatar_split_clause,[],[f705,f637,f388,f354,f724])).
% 0.21/0.53  fof(f354,plain,(
% 0.21/0.53    spl6_37 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.53  fof(f388,plain,(
% 0.21/0.53    spl6_45 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.21/0.53  fof(f637,plain,(
% 0.21/0.53    spl6_52 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.21/0.53  fof(f705,plain,(
% 0.21/0.53    sK4 = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | (~spl6_37 | ~spl6_45 | ~spl6_52)),
% 0.21/0.53    inference(superposition,[],[f605,f638])).
% 0.21/0.53  fof(f638,plain,(
% 0.21/0.53    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | ~spl6_52),
% 0.21/0.53    inference(avatar_component_clause,[],[f637])).
% 0.21/0.53  fof(f605,plain,(
% 0.21/0.53    ( ! [X0] : (k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),X0)) ) | (~spl6_37 | ~spl6_45)),
% 0.21/0.53    inference(subsumption_resolution,[],[f575,f355])).
% 0.21/0.53  fof(f355,plain,(
% 0.21/0.53    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~spl6_37),
% 0.21/0.53    inference(avatar_component_clause,[],[f354])).
% 0.21/0.53  fof(f575,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),X0)) ) | ~spl6_45),
% 0.21/0.53    inference(resolution,[],[f389,f53])).
% 0.21/0.53  fof(f389,plain,(
% 0.21/0.53    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1))) | ~spl6_45),
% 0.21/0.53    inference(avatar_component_clause,[],[f388])).
% 0.21/0.53  fof(f665,plain,(
% 0.21/0.53    spl6_53 | ~spl6_34 | ~spl6_42 | ~spl6_51),
% 0.21/0.53    inference(avatar_split_clause,[],[f644,f633,f376,f322,f663])).
% 0.21/0.53  fof(f322,plain,(
% 0.21/0.53    spl6_34 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    spl6_42 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.53  fof(f633,plain,(
% 0.21/0.53    spl6_51 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 0.21/0.53  fof(f644,plain,(
% 0.21/0.53    sK5 = k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | (~spl6_34 | ~spl6_42 | ~spl6_51)),
% 0.21/0.53    inference(superposition,[],[f430,f634])).
% 0.21/0.53  fof(f634,plain,(
% 0.21/0.53    sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | ~spl6_51),
% 0.21/0.53    inference(avatar_component_clause,[],[f633])).
% 0.21/0.53  fof(f430,plain,(
% 0.21/0.53    ( ! [X0] : (k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),X0)) ) | (~spl6_34 | ~spl6_42)),
% 0.21/0.53    inference(subsumption_resolution,[],[f400,f323])).
% 0.21/0.53  fof(f323,plain,(
% 0.21/0.53    v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~spl6_34),
% 0.21/0.53    inference(avatar_component_clause,[],[f322])).
% 0.21/0.53  fof(f400,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),X0)) ) | ~spl6_42),
% 0.21/0.53    inference(resolution,[],[f377,f53])).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1))) | ~spl6_42),
% 0.21/0.53    inference(avatar_component_clause,[],[f376])).
% 0.21/0.53  fof(f639,plain,(
% 0.21/0.53    spl6_52 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17 | ~spl6_37 | ~spl6_41 | ~spl6_45),
% 0.21/0.53    inference(avatar_split_clause,[],[f592,f388,f372,f354,f168,f129,f112,f90,f86,f82,f74,f637])).
% 0.21/0.53  fof(f372,plain,(
% 0.21/0.53    spl6_41 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.53  fof(f592,plain,(
% 0.21/0.53    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17 | ~spl6_37 | ~spl6_41 | ~spl6_45)),
% 0.21/0.53    inference(subsumption_resolution,[],[f591,f91])).
% 0.21/0.53  fof(f591,plain,(
% 0.21/0.53    v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | (~spl6_2 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_13 | ~spl6_17 | ~spl6_37 | ~spl6_41 | ~spl6_45)),
% 0.21/0.53    inference(subsumption_resolution,[],[f590,f373])).
% 0.21/0.53  fof(f373,plain,(
% 0.21/0.53    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | ~spl6_41),
% 0.21/0.53    inference(avatar_component_clause,[],[f372])).
% 0.21/0.53  fof(f590,plain,(
% 0.21/0.53    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | (~spl6_2 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_13 | ~spl6_17 | ~spl6_37 | ~spl6_45)),
% 0.21/0.53    inference(subsumption_resolution,[],[f589,f355])).
% 0.21/0.53  fof(f589,plain,(
% 0.21/0.53    ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | (~spl6_2 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_13 | ~spl6_17 | ~spl6_45)),
% 0.21/0.53    inference(subsumption_resolution,[],[f588,f169])).
% 0.21/0.53  fof(f588,plain,(
% 0.21/0.53    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | (~spl6_2 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_13 | ~spl6_45)),
% 0.21/0.53    inference(subsumption_resolution,[],[f587,f113])).
% 0.21/0.53  fof(f587,plain,(
% 0.21/0.53    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | (~spl6_2 | spl6_4 | spl6_5 | ~spl6_13 | ~spl6_45)),
% 0.21/0.53    inference(subsumption_resolution,[],[f586,f75])).
% 0.21/0.53  fof(f586,plain,(
% 0.21/0.53    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | (spl6_4 | spl6_5 | ~spl6_13 | ~spl6_45)),
% 0.21/0.53    inference(subsumption_resolution,[],[f585,f130])).
% 0.21/0.53  fof(f585,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | (spl6_4 | spl6_5 | ~spl6_45)),
% 0.21/0.53    inference(subsumption_resolution,[],[f584,f83])).
% 0.21/0.53  fof(f584,plain,(
% 0.21/0.53    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | (spl6_5 | ~spl6_45)),
% 0.21/0.53    inference(subsumption_resolution,[],[f583,f87])).
% 0.21/0.53  fof(f583,plain,(
% 0.21/0.53    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | ~spl6_45),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f582])).
% 0.21/0.53  fof(f582,plain,(
% 0.21/0.53    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK2)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK2)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | ~spl6_45),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f566])).
% 0.21/0.53  fof(f566,plain,(
% 0.21/0.53    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK2)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK2)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK2),sK1,k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),sK2) | ~spl6_45),
% 0.21/0.53    inference(resolution,[],[f389,f68])).
% 0.21/0.53  fof(f635,plain,(
% 0.21/0.53    spl6_51 | ~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16 | ~spl6_34 | ~spl6_38 | ~spl6_42),
% 0.21/0.53    inference(avatar_split_clause,[],[f417,f376,f360,f322,f162,f120,f105,f90,f86,f78,f70,f633])).
% 0.21/0.53  fof(f360,plain,(
% 0.21/0.53    spl6_38 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.53  fof(f417,plain,(
% 0.21/0.53    sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16 | ~spl6_34 | ~spl6_38 | ~spl6_42)),
% 0.21/0.53    inference(subsumption_resolution,[],[f416,f91])).
% 0.21/0.53  fof(f416,plain,(
% 0.21/0.53    v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | (~spl6_1 | spl6_3 | spl6_5 | ~spl6_9 | ~spl6_12 | ~spl6_16 | ~spl6_34 | ~spl6_38 | ~spl6_42)),
% 0.21/0.53    inference(subsumption_resolution,[],[f415,f361])).
% 0.21/0.53  fof(f361,plain,(
% 0.21/0.53    v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | ~spl6_38),
% 0.21/0.53    inference(avatar_component_clause,[],[f360])).
% 0.21/0.53  fof(f415,plain,(
% 0.21/0.53    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | (~spl6_1 | spl6_3 | spl6_5 | ~spl6_9 | ~spl6_12 | ~spl6_16 | ~spl6_34 | ~spl6_42)),
% 0.21/0.53    inference(subsumption_resolution,[],[f414,f323])).
% 0.21/0.53  fof(f414,plain,(
% 0.21/0.53    ~v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | (~spl6_1 | spl6_3 | spl6_5 | ~spl6_9 | ~spl6_12 | ~spl6_16 | ~spl6_42)),
% 0.21/0.53    inference(subsumption_resolution,[],[f413,f163])).
% 0.21/0.53  fof(f413,plain,(
% 0.21/0.53    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | (~spl6_1 | spl6_3 | spl6_5 | ~spl6_9 | ~spl6_12 | ~spl6_42)),
% 0.21/0.53    inference(subsumption_resolution,[],[f412,f106])).
% 0.21/0.53  fof(f412,plain,(
% 0.21/0.53    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | (~spl6_1 | spl6_3 | spl6_5 | ~spl6_12 | ~spl6_42)),
% 0.21/0.53    inference(subsumption_resolution,[],[f411,f71])).
% 0.21/0.54  fof(f411,plain,(
% 0.21/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | (spl6_3 | spl6_5 | ~spl6_12 | ~spl6_42)),
% 0.21/0.54    inference(subsumption_resolution,[],[f410,f121])).
% 0.21/0.54  fof(f410,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | (spl6_3 | spl6_5 | ~spl6_42)),
% 0.21/0.54    inference(subsumption_resolution,[],[f409,f79])).
% 0.21/0.54  fof(f409,plain,(
% 0.21/0.54    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | (spl6_5 | ~spl6_42)),
% 0.21/0.54    inference(subsumption_resolution,[],[f408,f87])).
% 0.21/0.54  fof(f408,plain,(
% 0.21/0.54    v1_xboole_0(sK1) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | ~spl6_42),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f407])).
% 0.21/0.54  fof(f407,plain,(
% 0.21/0.54    v1_xboole_0(sK1) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK3,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK3,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | ~spl6_42),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f391])).
% 0.21/0.54  fof(f391,plain,(
% 0.21/0.54    v1_xboole_0(sK1) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK3,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK3,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK3,sK3),sK1,k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),sK3) | ~spl6_42),
% 0.21/0.54    inference(resolution,[],[f377,f68])).
% 0.21/0.54  fof(f620,plain,(
% 0.21/0.54    spl6_50 | ~spl6_45),
% 0.21/0.54    inference(avatar_split_clause,[],[f574,f388,f618])).
% 0.21/0.54  fof(f574,plain,(
% 0.21/0.54    v1_relat_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | ~spl6_45),
% 0.21/0.54    inference(resolution,[],[f389,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f565,plain,(
% 0.21/0.54    ~spl6_47 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_36 | ~spl6_40 | ~spl6_44),
% 0.21/0.54    inference(avatar_split_clause,[],[f548,f384,f368,f350,f197,f168,f162,f158,f129,f120,f112,f105,f90,f86,f82,f78,f74,f70,f563])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    spl6_20 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.54  fof(f548,plain,(
% 0.21/0.54    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.54    inference(forward_demodulation,[],[f547,f192])).
% 0.21/0.54  fof(f547,plain,(
% 0.21/0.54    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.54    inference(forward_demodulation,[],[f546,f159])).
% 0.21/0.54  fof(f546,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.54    inference(forward_demodulation,[],[f545,f137])).
% 0.21/0.54  fof(f545,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.54    inference(forward_demodulation,[],[f544,f181])).
% 0.21/0.54  fof(f544,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f543,f198])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | spl6_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f197])).
% 0.21/0.54  fof(f543,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f542,f91])).
% 0.21/0.54  fof(f542,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | ~spl6_36 | ~spl6_40 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f541,f369])).
% 0.21/0.54  fof(f541,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | ~spl6_36 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f540,f351])).
% 0.21/0.54  fof(f540,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f539,f163])).
% 0.21/0.54  fof(f539,plain,(
% 0.21/0.54    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f538,f106])).
% 0.21/0.54  fof(f538,plain,(
% 0.21/0.54    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f537,f71])).
% 0.21/0.54  fof(f537,plain,(
% 0.21/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_17 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f536,f169])).
% 0.21/0.54  fof(f536,plain,(
% 0.21/0.54    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f535,f113])).
% 0.21/0.54  fof(f535,plain,(
% 0.21/0.54    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_13 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f534,f75])).
% 0.21/0.54  fof(f534,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_13 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f533,f121])).
% 0.21/0.54  fof(f533,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_13 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f532,f79])).
% 0.21/0.54  fof(f532,plain,(
% 0.21/0.54    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_4 | spl6_5 | ~spl6_13 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f531,f130])).
% 0.21/0.54  fof(f531,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_4 | spl6_5 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f530,f83])).
% 0.21/0.54  fof(f530,plain,(
% 0.21/0.54    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_5 | ~spl6_44)),
% 0.21/0.54    inference(subsumption_resolution,[],[f499,f87])).
% 0.21/0.54  fof(f499,plain,(
% 0.21/0.54    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl6_44),
% 0.21/0.54    inference(resolution,[],[f385,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.21/0.54    inference(equality_resolution,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f497,plain,(
% 0.21/0.54    spl6_46 | ~spl6_42),
% 0.21/0.54    inference(avatar_split_clause,[],[f399,f376,f495])).
% 0.21/0.54  fof(f399,plain,(
% 0.21/0.54    v1_relat_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | ~spl6_42),
% 0.21/0.54    inference(resolution,[],[f377,f55])).
% 0.21/0.54  fof(f390,plain,(
% 0.21/0.54    spl6_45 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f348,f168,f129,f112,f90,f86,f82,f74,f388])).
% 0.21/0.54  fof(f348,plain,(
% 0.21/0.54    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f347,f83])).
% 0.21/0.54  fof(f347,plain,(
% 0.21/0.54    v1_xboole_0(sK2) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f346,f113])).
% 0.21/0.54  fof(f346,plain,(
% 0.21/0.54    ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK2) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f345,f75])).
% 0.21/0.54  fof(f345,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK2) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f340,f130])).
% 0.21/0.54  fof(f340,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK2) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK2),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(resolution,[],[f249,f169])).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f248,f87])).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f247,f113])).
% 0.21/0.54  fof(f247,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f246,f75])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (spl6_4 | spl6_6 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(resolution,[],[f156,f169])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X12,X10,X11,X9] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | v1_xboole_0(X9) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | (spl6_4 | spl6_6 | ~spl6_13)),
% 0.21/0.54    inference(subsumption_resolution,[],[f155,f91])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X12,X10,X11,X9] : (v1_xboole_0(X9) | v1_xboole_0(sK0) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | (spl6_4 | ~spl6_13)),
% 0.21/0.54    inference(subsumption_resolution,[],[f150,f83])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ( ! [X12,X10,X11,X9] : (v1_xboole_0(X9) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | ~spl6_13),
% 0.21/0.54    inference(resolution,[],[f130,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.21/0.54  fof(f386,plain,(
% 0.21/0.54    spl6_44 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f344,f168,f162,f129,f120,f112,f105,f90,f86,f82,f78,f74,f70,f384])).
% 0.21/0.54  fof(f344,plain,(
% 0.21/0.54    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f343,f79])).
% 0.21/0.54  fof(f343,plain,(
% 0.21/0.54    v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f342,f106])).
% 0.21/0.54  fof(f342,plain,(
% 0.21/0.54    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f341,f71])).
% 0.21/0.54  fof(f341,plain,(
% 0.21/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f339,f121])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(resolution,[],[f249,f163])).
% 0.21/0.54  fof(f378,plain,(
% 0.21/0.54    spl6_42 | ~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f330,f162,f120,f105,f90,f86,f78,f70,f376])).
% 0.21/0.54  fof(f330,plain,(
% 0.21/0.54    m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1))) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f329,f79])).
% 0.21/0.54  fof(f329,plain,(
% 0.21/0.54    v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1))) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f328,f106])).
% 0.21/0.54  fof(f328,plain,(
% 0.21/0.54    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1))) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f327,f71])).
% 0.21/0.54  fof(f327,plain,(
% 0.21/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1))) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f325,f121])).
% 0.21/0.54  fof(f325,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,sK3),sK1))) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(resolution,[],[f245,f163])).
% 0.21/0.54  fof(f245,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X0),sK1)))) ) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f244,f87])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X0),sK1)))) ) | (~spl6_1 | spl6_3 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f243,f106])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X0),sK1)))) ) | (~spl6_1 | spl6_3 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f242,f71])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X0),sK1)))) ) | (spl6_3 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(resolution,[],[f146,f163])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ( ! [X12,X10,X11,X9] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK3,X9))) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK3,X9) | v1_xboole_0(X9) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK3,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X10),X9)))) ) | (spl6_3 | spl6_6 | ~spl6_12)),
% 0.21/0.54    inference(subsumption_resolution,[],[f145,f91])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X12,X10,X11,X9] : (v1_xboole_0(X9) | v1_xboole_0(sK0) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK3,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK3,X9))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK3,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X10),X9)))) ) | (spl6_3 | ~spl6_12)),
% 0.21/0.54    inference(subsumption_resolution,[],[f140,f79])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    ( ! [X12,X10,X11,X9] : (v1_xboole_0(X9) | v1_xboole_0(sK3) | v1_xboole_0(sK0) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK3,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK3,X9))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK3,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK3,X10),X9)))) ) | ~spl6_12),
% 0.21/0.54    inference(resolution,[],[f121,f49])).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    spl6_41 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f320,f168,f129,f112,f90,f86,f82,f74,f372])).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f319,f83])).
% 0.21/0.54  fof(f319,plain,(
% 0.21/0.54    v1_xboole_0(sK2) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f318,f113])).
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK2) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f317,f75])).
% 0.21/0.54  fof(f317,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK2) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f312,f130])).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK2) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4),k4_subset_1(sK0,sK2,sK2),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(resolution,[],[f241,f169])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f240,f87])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f239,f113])).
% 0.21/0.54  fof(f239,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f238,f75])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (spl6_4 | spl6_6 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(resolution,[],[f154,f169])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | v1_xboole_0(X5) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | (spl6_4 | spl6_6 | ~spl6_13)),
% 0.21/0.54    inference(subsumption_resolution,[],[f153,f91])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    ( ! [X6,X8,X7,X5] : (v1_xboole_0(X5) | v1_xboole_0(sK0) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | (spl6_4 | ~spl6_13)),
% 0.21/0.54    inference(subsumption_resolution,[],[f149,f83])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X6,X8,X7,X5] : (v1_xboole_0(X5) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | ~spl6_13),
% 0.21/0.54    inference(resolution,[],[f130,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f370,plain,(
% 0.21/0.54    spl6_40 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f316,f168,f162,f129,f120,f112,f105,f90,f86,f82,f78,f74,f70,f368])).
% 0.21/0.54  fof(f316,plain,(
% 0.21/0.54    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f315,f79])).
% 0.21/0.54  fof(f315,plain,(
% 0.21/0.54    v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f314,f106])).
% 0.21/0.54  fof(f314,plain,(
% 0.21/0.54    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f313,f71])).
% 0.21/0.54  fof(f313,plain,(
% 0.21/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f311,f121])).
% 0.21/0.54  fof(f311,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(resolution,[],[f241,f163])).
% 0.21/0.54  fof(f362,plain,(
% 0.21/0.54    spl6_38 | ~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f306,f162,f120,f105,f90,f86,f78,f70,f360])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f305,f79])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f304,f106])).
% 0.21/0.54  fof(f304,plain,(
% 0.21/0.54    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f303,f71])).
% 0.21/0.54  fof(f303,plain,(
% 0.21/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f301,f121])).
% 0.21/0.54  fof(f301,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5),k4_subset_1(sK0,sK3,sK3),sK1) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(resolution,[],[f233,f163])).
% 0.21/0.54  fof(f233,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k4_subset_1(sK0,sK3,X0),sK1)) ) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f232,f87])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k4_subset_1(sK0,sK3,X0),sK1)) ) | (~spl6_1 | spl6_3 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f231,f106])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k4_subset_1(sK0,sK3,X0),sK1)) ) | (~spl6_1 | spl6_3 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f230,f71])).
% 0.21/0.54  fof(f230,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1),k4_subset_1(sK0,sK3,X0),sK1)) ) | (spl6_3 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(resolution,[],[f144,f163])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,X5))) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK3,X5) | v1_xboole_0(X5) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK3,X6,X7,X8),k4_subset_1(sK0,sK3,X6),X5)) ) | (spl6_3 | spl6_6 | ~spl6_12)),
% 0.21/0.54    inference(subsumption_resolution,[],[f143,f91])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ( ! [X6,X8,X7,X5] : (v1_xboole_0(X5) | v1_xboole_0(sK0) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK3,X5) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,X5))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK3,X6,X7,X8),k4_subset_1(sK0,sK3,X6),X5)) ) | (spl6_3 | ~spl6_12)),
% 0.21/0.54    inference(subsumption_resolution,[],[f139,f79])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ( ! [X6,X8,X7,X5] : (v1_xboole_0(X5) | v1_xboole_0(sK3) | v1_xboole_0(sK0) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK3,X5) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,X5))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK3,X6,X7,X8),k4_subset_1(sK0,sK3,X6),X5)) ) | ~spl6_12),
% 0.21/0.54    inference(resolution,[],[f121,f48])).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    spl6_37 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f300,f168,f129,f112,f90,f86,f82,f74,f354])).
% 0.21/0.54  fof(f300,plain,(
% 0.21/0.54    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f299,f83])).
% 0.21/0.54  fof(f299,plain,(
% 0.21/0.54    v1_xboole_0(sK2) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f298,f113])).
% 0.21/0.54  fof(f298,plain,(
% 0.21/0.54    ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK2) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f297,f75])).
% 0.21/0.54  fof(f297,plain,(
% 0.21/0.54    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK2) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f292,f130])).
% 0.21/0.54  fof(f292,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK2) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK2,sK4,sK4)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(resolution,[],[f225,f169])).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f224,f87])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f223,f113])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f222,f75])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (spl6_4 | spl6_6 | ~spl6_13 | ~spl6_17)),
% 0.21/0.54    inference(resolution,[],[f152,f169])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X4,X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | v1_xboole_0(X1) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | (spl6_4 | spl6_6 | ~spl6_13)),
% 0.21/0.54    inference(subsumption_resolution,[],[f151,f91])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ( ! [X4,X2,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | (spl6_4 | ~spl6_13)),
% 0.21/0.54    inference(subsumption_resolution,[],[f148,f83])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ( ! [X4,X2,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | ~spl6_13),
% 0.21/0.54    inference(resolution,[],[f130,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f352,plain,(
% 0.21/0.54    spl6_36 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f296,f168,f162,f129,f120,f112,f105,f90,f86,f82,f78,f74,f70,f350])).
% 0.21/0.54  fof(f296,plain,(
% 0.21/0.54    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f295,f79])).
% 0.21/0.54  fof(f295,plain,(
% 0.21/0.54    v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f294,f106])).
% 0.21/0.54  fof(f294,plain,(
% 0.21/0.54    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f293,f71])).
% 0.21/0.54  fof(f293,plain,(
% 0.21/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f291,f121])).
% 0.21/0.54  fof(f291,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_13 | ~spl6_16 | ~spl6_17)),
% 0.21/0.54    inference(resolution,[],[f225,f163])).
% 0.21/0.54  fof(f324,plain,(
% 0.21/0.54    spl6_34 | ~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f282,f162,f120,f105,f90,f86,f78,f70,f322])).
% 0.21/0.54  fof(f282,plain,(
% 0.21/0.54    v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f281,f79])).
% 0.21/0.54  fof(f281,plain,(
% 0.21/0.54    v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f280,f106])).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f279,f71])).
% 0.21/0.54  fof(f279,plain,(
% 0.21/0.54    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f277,f121])).
% 0.21/0.54  fof(f277,plain,(
% 0.21/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,sK3,sK5,sK5)) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(resolution,[],[f219,f163])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1))) ) | (~spl6_1 | spl6_3 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f218,f87])).
% 0.21/0.54  fof(f218,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1))) ) | (~spl6_1 | spl6_3 | spl6_6 | ~spl6_9 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f217,f106])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1))) ) | (~spl6_1 | spl6_3 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f216,f71])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK3,X0,sK5,X1))) ) | (spl6_3 | spl6_6 | ~spl6_12 | ~spl6_16)),
% 0.21/0.54    inference(resolution,[],[f142,f163])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    ( ! [X4,X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK3,X1) | v1_xboole_0(X1) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK3,X2,X3,X4))) ) | (spl6_3 | spl6_6 | ~spl6_12)),
% 0.21/0.54    inference(subsumption_resolution,[],[f141,f91])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X4,X2,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK3,X2,X3,X4))) ) | (spl6_3 | ~spl6_12)),
% 0.21/0.54    inference(subsumption_resolution,[],[f138,f79])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X4,X2,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(sK3) | v1_xboole_0(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK3,X2,X3,X4))) ) | ~spl6_12),
% 0.21/0.54    inference(resolution,[],[f121,f47])).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    spl6_23 | ~spl6_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f186,f168,f207])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    v1_relat_1(sK4) | ~spl6_17),
% 0.21/0.54    inference(resolution,[],[f169,f55])).
% 0.21/0.54  fof(f205,plain,(
% 0.21/0.54    ~spl6_20 | ~spl6_21 | ~spl6_22),
% 0.21/0.54    inference(avatar_split_clause,[],[f33,f203,f200,f197])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f14])).
% 0.21/0.54  fof(f14,conjecture,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    spl6_19 | ~spl6_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f175,f162,f183])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    v1_relat_1(sK5) | ~spl6_16),
% 0.21/0.54    inference(resolution,[],[f163,f55])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    spl6_17),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f168])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    spl6_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f162])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    spl6_15 | ~spl6_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f109,f101,f158])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl6_8),
% 0.21/0.54    inference(resolution,[],[f102,f60])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    spl6_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f129])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    spl6_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f120])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    spl6_11 | ~spl6_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f108,f101,f116])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    r1_xboole_0(sK3,sK2) | ~spl6_8),
% 0.21/0.54    inference(resolution,[],[f102,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    spl6_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f112])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    v1_funct_2(sK4,sK2,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    spl6_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f35,f105])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    v1_funct_2(sK5,sK3,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    spl6_8 | spl6_3 | spl6_4 | ~spl6_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f99,f94,f82,f78,f101])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl6_7 <=> r1_subset_1(sK2,sK3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    r1_xboole_0(sK2,sK3) | (spl6_3 | spl6_4 | ~spl6_7)),
% 0.21/0.54    inference(subsumption_resolution,[],[f98,f83])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | (spl6_3 | ~spl6_7)),
% 0.21/0.54    inference(subsumption_resolution,[],[f97,f79])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl6_7),
% 0.21/0.54    inference(resolution,[],[f95,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    r1_subset_1(sK2,sK3) | ~spl6_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f94])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl6_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f94])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    r1_subset_1(sK2,sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ~spl6_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f46,f90])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ~spl6_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f86])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~v1_xboole_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ~spl6_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f82])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ~v1_xboole_0(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ~spl6_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f78])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ~v1_xboole_0(sK3)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    spl6_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f37,f74])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    v1_funct_1(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    spl6_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f34,f70])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v1_funct_1(sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (5780)------------------------------
% 0.21/0.54  % (5780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5780)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (5780)Memory used [KB]: 7164
% 0.21/0.54  % (5780)Time elapsed: 0.089 s
% 0.21/0.54  % (5780)------------------------------
% 0.21/0.54  % (5780)------------------------------
% 0.21/0.54  % (5779)Success in time 0.186 s
%------------------------------------------------------------------------------
