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
% DateTime   : Thu Dec  3 13:17:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  259 ( 614 expanded)
%              Number of leaves         :   41 ( 230 expanded)
%              Depth                    :   28
%              Number of atoms          : 1953 (3555 expanded)
%              Number of equality atoms :  168 ( 402 expanded)
%              Maximal formula depth    :   26 (   9 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f586,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f86,f90,f94,f101,f105,f111,f115,f119,f143,f147,f153,f173,f183,f187,f193,f197,f205,f209,f224,f322,f355,f371,f387,f555,f577,f585])).

% (20885)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f585,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_19
    | ~ spl6_25
    | ~ spl6_35 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_19
    | ~ spl6_25
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f583,f223])).

fof(f223,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl6_25
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f583,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_19
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f582,f321])).

fof(f321,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl6_35
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f582,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_19 ),
    inference(forward_demodulation,[],[f581,f169])).

fof(f169,plain,
    ( ! [X0] : k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl6_2
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f164,f73])).

fof(f73,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_2
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) )
    | ~ spl6_15 ),
    inference(resolution,[],[f152,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f152,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl6_15
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f581,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_19 ),
    inference(forward_demodulation,[],[f580,f142])).

fof(f142,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl6_13
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f580,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_11
    | ~ spl6_14
    | spl6_19 ),
    inference(forward_demodulation,[],[f579,f120])).

fof(f120,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)
    | ~ spl6_11 ),
    inference(resolution,[],[f114,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f114,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f579,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_14
    | spl6_19 ),
    inference(forward_demodulation,[],[f182,f161])).

fof(f161,plain,
    ( ! [X0] : k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | ~ spl6_1
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f156,f69])).

fof(f69,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_1
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK5)
        | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) )
    | ~ spl6_14 ),
    inference(resolution,[],[f146,f52])).

fof(f146,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_14
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f182,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl6_19
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f577,plain,
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
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_18
    | ~ spl6_25
    | ~ spl6_35
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
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
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_18
    | ~ spl6_25
    | ~ spl6_35
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f179,f533])).

fof(f533,plain,
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
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_25
    | ~ spl6_35
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f532,f223])).

fof(f532,plain,
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
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_35
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f531,f321])).

fof(f531,plain,
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
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f530,f169])).

fof(f530,plain,
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
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f529,f142])).

fof(f529,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f528,f120])).

fof(f528,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f527,f161])).

fof(f527,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f526,f89])).

fof(f89,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f526,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f525,f370])).

fof(f370,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl6_42
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f525,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f524,f354])).

fof(f354,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl6_38
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f524,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f523,f146])).

fof(f523,plain,
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
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f522,f104])).

fof(f104,plain,
    ( v1_funct_2(sK5,sK3,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_9
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f522,plain,
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
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f521,f69])).

fof(f521,plain,
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
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f520,f152])).

fof(f520,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f519,f110])).

fof(f110,plain,
    ( v1_funct_2(sK4,sK2,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_10
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f519,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f518,f73])).

fof(f518,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f517,f114])).

fof(f517,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f516,f77])).

fof(f77,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_3
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f516,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f515,f118])).

fof(f118,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f515,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f514,f81])).

fof(f81,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f514,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f499,f85])).

fof(f85,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

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
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_46 ),
    inference(resolution,[],[f386,f66])).

fof(f66,plain,(
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
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f386,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl6_46
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f179,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl6_18
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f555,plain,
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
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_17
    | ~ spl6_25
    | ~ spl6_35
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
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
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_17
    | ~ spl6_25
    | ~ spl6_35
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f553,f223])).

fof(f553,plain,
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
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_17
    | ~ spl6_35
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f552,f321])).

fof(f552,plain,
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
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_17
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f551,f169])).

fof(f551,plain,
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
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_17
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f550,f142])).

fof(f550,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | spl6_17
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f549,f120])).

fof(f549,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | spl6_17
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(forward_demodulation,[],[f548,f161])).

fof(f548,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | spl6_17
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f547,f176])).

fof(f176,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl6_17
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f547,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f546,f89])).

fof(f546,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f545,f370])).

fof(f545,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_38
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f544,f354])).

fof(f544,plain,
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
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f543,f146])).

% (20900)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f543,plain,
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
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f542,f104])).

% (20894)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (20885)Refutation not found, incomplete strategy% (20885)------------------------------
% (20885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20885)Termination reason: Refutation not found, incomplete strategy

% (20885)Memory used [KB]: 10746
% (20885)Time elapsed: 0.094 s
% (20885)------------------------------
% (20885)------------------------------
fof(f542,plain,
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
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f541,f69])).

fof(f541,plain,
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
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f540,f152])).

fof(f540,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f539,f110])).

fof(f539,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f538,f73])).

fof(f538,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f537,f114])).

fof(f537,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f536,f77])).

fof(f536,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f535,f118])).

fof(f535,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f534,f81])).

fof(f534,plain,
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
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f500,f85])).

fof(f500,plain,
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
    | ~ spl6_46 ),
    inference(resolution,[],[f386,f65])).

fof(f65,plain,(
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
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f387,plain,
    ( spl6_46
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f339,f151,f145,f117,f113,f109,f103,f88,f84,f80,f76,f72,f68,f385])).

fof(f339,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f338,f77])).

fof(f338,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f337,f104])).

fof(f337,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f336,f69])).

fof(f336,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f334,f114])).

fof(f334,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(resolution,[],[f245,f146])).

fof(f245,plain,
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
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f244,f85])).

fof(f244,plain,
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
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f243,f110])).

fof(f243,plain,
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
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f242,f73])).

fof(f242,plain,
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
    | ~ spl6_15 ),
    inference(resolution,[],[f139,f152])).

fof(f139,plain,
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
    inference(subsumption_resolution,[],[f138,f89])).

fof(f138,plain,
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
    inference(subsumption_resolution,[],[f133,f81])).

fof(f133,plain,
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
    inference(resolution,[],[f118,f48])).

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
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f371,plain,
    ( spl6_42
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f314,f151,f145,f117,f113,f109,f103,f88,f84,f80,f76,f72,f68,f369])).

fof(f314,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f313,f77])).

fof(f313,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f312,f104])).

fof(f312,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f311,f69])).

fof(f311,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f309,f114])).

fof(f309,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(resolution,[],[f233,f146])).

fof(f233,plain,
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
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f232,f85])).

fof(f232,plain,
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
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f231,f110])).

fof(f231,plain,
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
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f230,f73])).

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
        | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1) )
    | spl6_4
    | spl6_6
    | ~ spl6_12
    | ~ spl6_15 ),
    inference(resolution,[],[f137,f152])).

fof(f137,plain,
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
    inference(subsumption_resolution,[],[f136,f89])).

fof(f136,plain,
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
    inference(subsumption_resolution,[],[f132,f81])).

fof(f132,plain,
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
    inference(resolution,[],[f118,f47])).

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
      | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f355,plain,
    ( spl6_38
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f292,f151,f145,f117,f113,f109,f103,f88,f84,f80,f76,f72,f68,f353])).

fof(f292,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f291,f77])).

fof(f291,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f290,f104])).

fof(f290,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f289,f69])).

fof(f289,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f287,f114])).

fof(f287,plain,
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
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(resolution,[],[f220,f146])).

fof(f220,plain,
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
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f219,f85])).

fof(f219,plain,
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
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f218,f110])).

fof(f218,plain,
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
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f217,f73])).

fof(f217,plain,
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
    | ~ spl6_15 ),
    inference(resolution,[],[f135,f152])).

fof(f135,plain,
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
    inference(subsumption_resolution,[],[f134,f89])).

fof(f134,plain,
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
    inference(subsumption_resolution,[],[f131,f81])).

fof(f131,plain,
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
    inference(resolution,[],[f118,f46])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f18])).

fof(f322,plain,
    ( spl6_35
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f307,f207,f185,f320])).

% (20904)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f185,plain,
    ( spl6_20
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f207,plain,
    ( spl6_24
  <=> sK4 = k7_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f307,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(superposition,[],[f270,f208])).

fof(f208,plain,
    ( sK4 = k7_relat_1(sK4,sK2)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f207])).

fof(f270,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0)
    | ~ spl6_20 ),
    inference(resolution,[],[f189,f61])).

fof(f61,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),X1) )
    | ~ spl6_20 ),
    inference(resolution,[],[f186,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f186,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f224,plain,
    ( spl6_25
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f216,f203,f171,f222])).

fof(f171,plain,
    ( spl6_16
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f203,plain,
    ( spl6_23
  <=> sK5 = k7_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f216,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_16
    | ~ spl6_23 ),
    inference(superposition,[],[f210,f204])).

fof(f204,plain,
    ( sK5 = k7_relat_1(sK5,sK3)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f203])).

fof(f210,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0)
    | ~ spl6_16 ),
    inference(resolution,[],[f188,f61])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X0),X1) )
    | ~ spl6_16 ),
    inference(resolution,[],[f172,f57])).

fof(f172,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f171])).

% (20888)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f209,plain,
    ( spl6_24
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f201,f195,f185,f207])).

fof(f195,plain,
    ( spl6_22
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f201,plain,
    ( sK4 = k7_relat_1(sK4,sK2)
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f200,f186])).

fof(f200,plain,
    ( ~ v1_relat_1(sK4)
    | sK4 = k7_relat_1(sK4,sK2)
    | ~ spl6_22 ),
    inference(resolution,[],[f196,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f196,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f195])).

fof(f205,plain,
    ( spl6_23
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f199,f191,f171,f203])).

fof(f191,plain,
    ( spl6_21
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f199,plain,
    ( sK5 = k7_relat_1(sK5,sK3)
    | ~ spl6_16
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f198,f172])).

fof(f198,plain,
    ( ~ v1_relat_1(sK5)
    | sK5 = k7_relat_1(sK5,sK3)
    | ~ spl6_21 ),
    inference(resolution,[],[f192,f58])).

fof(f192,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f191])).

% (20905)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f197,plain,
    ( spl6_22
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f162,f151,f195])).

fof(f162,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_15 ),
    inference(resolution,[],[f152,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f193,plain,
    ( spl6_21
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f154,f145,f191])).

fof(f154,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_14 ),
    inference(resolution,[],[f146,f62])).

fof(f187,plain,
    ( spl6_20
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f163,f151,f185])).

fof(f163,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_15 ),
    inference(resolution,[],[f152,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f183,plain,
    ( ~ spl6_17
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f32,f181,f178,f175])).

fof(f32,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

% (20902)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f12,conjecture,(
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

fof(f173,plain,
    ( spl6_16
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f155,f145,f171])).

fof(f155,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_14 ),
    inference(resolution,[],[f146,f54])).

fof(f153,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f38,f151])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f147,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f35,f145])).

fof(f35,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f143,plain,
    ( spl6_13
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f106,f99,f141])).

fof(f99,plain,
    ( spl6_8
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f106,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3)
    | ~ spl6_8 ),
    inference(resolution,[],[f100,f60])).

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

fof(f100,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f119,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f43,f117])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f115,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f40,f113])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f111,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f37,f109])).

fof(f37,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f105,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f34,f103])).

fof(f34,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f101,plain,
    ( spl6_8
    | spl6_3
    | spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f97,f92,f80,f76,f99])).

fof(f92,plain,
    ( spl6_7
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f97,plain,
    ( r1_xboole_0(sK2,sK3)
    | spl6_3
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f96,f81])).

fof(f96,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f95,f77])).

fof(f95,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f93,f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f93,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f94,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f41,f92])).

fof(f41,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f42,f80])).

fof(f42,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f36,f72])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:25:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (20890)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.45  % (20897)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (20884)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (20901)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (20898)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (20891)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (20886)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (20884)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (20892)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (20889)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (20887)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f586,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f86,f90,f94,f101,f105,f111,f115,f119,f143,f147,f153,f173,f183,f187,f193,f197,f205,f209,f224,f322,f355,f371,f387,f555,f577,f585])).
% 0.22/0.50  % (20885)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  fof(f585,plain,(
% 0.22/0.50    ~spl6_1 | ~spl6_2 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_19 | ~spl6_25 | ~spl6_35),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f584])).
% 0.22/0.50  fof(f584,plain,(
% 0.22/0.50    $false | (~spl6_1 | ~spl6_2 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_19 | ~spl6_25 | ~spl6_35)),
% 0.22/0.50    inference(subsumption_resolution,[],[f583,f223])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl6_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f222])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    spl6_25 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.50  fof(f583,plain,(
% 0.22/0.50    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | (~spl6_1 | ~spl6_2 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_19 | ~spl6_35)),
% 0.22/0.50    inference(forward_demodulation,[],[f582,f321])).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl6_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f320])).
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    spl6_35 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.22/0.50  fof(f582,plain,(
% 0.22/0.50    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | (~spl6_1 | ~spl6_2 | ~spl6_11 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_19)),
% 0.22/0.50    inference(forward_demodulation,[],[f581,f169])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) ) | (~spl6_2 | ~spl6_15)),
% 0.22/0.50    inference(subsumption_resolution,[],[f164,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    v1_funct_1(sK4) | ~spl6_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl6_2 <=> v1_funct_1(sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_1(sK4) | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) ) | ~spl6_15),
% 0.22/0.50    inference(resolution,[],[f152,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f151])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    spl6_15 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.50  fof(f581,plain,(
% 0.22/0.50    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl6_1 | ~spl6_11 | ~spl6_13 | ~spl6_14 | spl6_19)),
% 0.22/0.50    inference(forward_demodulation,[],[f580,f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl6_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f141])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl6_13 <=> k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.50  fof(f580,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_11 | ~spl6_14 | spl6_19)),
% 0.22/0.50    inference(forward_demodulation,[],[f579,f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)) ) | ~spl6_11),
% 0.22/0.50    inference(resolution,[],[f114,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl6_11 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.50  fof(f579,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_14 | spl6_19)),
% 0.22/0.50    inference(forward_demodulation,[],[f182,f161])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    ( ! [X0] : (k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)) ) | (~spl6_1 | ~spl6_14)),
% 0.22/0.50    inference(subsumption_resolution,[],[f156,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    v1_funct_1(sK5) | ~spl6_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl6_1 <=> v1_funct_1(sK5)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_1(sK5) | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)) ) | ~spl6_14),
% 0.22/0.50    inference(resolution,[],[f146,f52])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f145])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    spl6_14 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f181])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    spl6_19 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.50  fof(f577,plain,(
% 0.22/0.50    ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_18 | ~spl6_25 | ~spl6_35 | ~spl6_38 | ~spl6_42 | ~spl6_46),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f576])).
% 0.22/0.50  fof(f576,plain,(
% 0.22/0.50    $false | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_18 | ~spl6_25 | ~spl6_35 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f179,f533])).
% 0.22/0.50  fof(f533,plain,(
% 0.22/0.50    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_25 | ~spl6_35 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f532,f223])).
% 0.22/0.50  fof(f532,plain,(
% 0.22/0.50    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_35 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f531,f321])).
% 0.22/0.50  fof(f531,plain,(
% 0.22/0.50    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f530,f169])).
% 0.22/0.50  fof(f530,plain,(
% 0.22/0.50    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f529,f142])).
% 0.22/0.50  fof(f529,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f528,f120])).
% 0.22/0.50  fof(f528,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f527,f161])).
% 0.22/0.50  fof(f527,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f526,f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ~v1_xboole_0(sK0) | spl6_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl6_6 <=> v1_xboole_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.50  fof(f526,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f525,f370])).
% 0.22/0.50  fof(f370,plain,(
% 0.22/0.50    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~spl6_42),
% 0.22/0.50    inference(avatar_component_clause,[],[f369])).
% 0.22/0.50  fof(f369,plain,(
% 0.22/0.50    spl6_42 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.22/0.50  fof(f525,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_38 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f524,f354])).
% 0.22/0.50  fof(f354,plain,(
% 0.22/0.50    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f353])).
% 0.22/0.50  fof(f353,plain,(
% 0.22/0.50    spl6_38 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.22/0.50  fof(f524,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f523,f146])).
% 0.22/0.50  fof(f523,plain,(
% 0.22/0.50    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f522,f104])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    v1_funct_2(sK5,sK3,sK1) | ~spl6_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl6_9 <=> v1_funct_2(sK5,sK3,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.50  fof(f522,plain,(
% 0.22/0.50    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f521,f69])).
% 0.22/0.50  fof(f521,plain,(
% 0.22/0.50    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f520,f152])).
% 0.22/0.50  fof(f520,plain,(
% 0.22/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f519,f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    v1_funct_2(sK4,sK2,sK1) | ~spl6_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f109])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl6_10 <=> v1_funct_2(sK4,sK2,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.50  fof(f519,plain,(
% 0.22/0.50    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f518,f73])).
% 0.22/0.50  fof(f518,plain,(
% 0.22/0.50    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f517,f114])).
% 0.22/0.50  fof(f517,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f516,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ~v1_xboole_0(sK3) | spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl6_3 <=> v1_xboole_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.50  fof(f516,plain,(
% 0.22/0.50    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_4 | spl6_5 | ~spl6_12 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f515,f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f117])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl6_12 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.50  fof(f515,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_4 | spl6_5 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f514,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ~v1_xboole_0(sK2) | spl6_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl6_4 <=> v1_xboole_0(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.50  fof(f514,plain,(
% 0.22/0.50    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_5 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f499,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ~v1_xboole_0(sK1) | spl6_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl6_5 <=> v1_xboole_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.50  fof(f499,plain,(
% 0.22/0.50    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl6_46),
% 0.22/0.50    inference(resolution,[],[f386,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.22/0.50    inference(equality_resolution,[],[f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.22/0.50  fof(f386,plain,(
% 0.22/0.50    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl6_46),
% 0.22/0.50    inference(avatar_component_clause,[],[f385])).
% 0.22/0.50  fof(f385,plain,(
% 0.22/0.50    spl6_46 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl6_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f178])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    spl6_18 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.50  fof(f555,plain,(
% 0.22/0.50    ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_17 | ~spl6_25 | ~spl6_35 | ~spl6_38 | ~spl6_42 | ~spl6_46),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f554])).
% 0.22/0.50  fof(f554,plain,(
% 0.22/0.50    $false | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_17 | ~spl6_25 | ~spl6_35 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f553,f223])).
% 0.22/0.50  fof(f553,plain,(
% 0.22/0.50    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_17 | ~spl6_35 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f552,f321])).
% 0.22/0.50  fof(f552,plain,(
% 0.22/0.50    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_17 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f551,f169])).
% 0.22/0.50  fof(f551,plain,(
% 0.22/0.50    k7_relat_1(sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_14 | ~spl6_15 | spl6_17 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f550,f142])).
% 0.22/0.50  fof(f550,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | spl6_17 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f549,f120])).
% 0.22/0.50  fof(f549,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | spl6_17 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f548,f161])).
% 0.22/0.50  fof(f548,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | spl6_17 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f547,f176])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | spl6_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f175])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    spl6_17 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.50  fof(f547,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f546,f89])).
% 0.22/0.50  fof(f546,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_38 | ~spl6_42 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f545,f370])).
% 0.22/0.50  fof(f545,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_38 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f544,f354])).
% 0.22/0.50  fof(f544,plain,(
% 0.22/0.50    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f543,f146])).
% 0.22/0.50  % (20900)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  fof(f543,plain,(
% 0.22/0.50    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f542,f104])).
% 0.22/0.50  % (20894)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (20885)Refutation not found, incomplete strategy% (20885)------------------------------
% 0.22/0.50  % (20885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (20885)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (20885)Memory used [KB]: 10746
% 0.22/0.50  % (20885)Time elapsed: 0.094 s
% 0.22/0.50  % (20885)------------------------------
% 0.22/0.50  % (20885)------------------------------
% 0.22/0.50  fof(f542,plain,(
% 0.22/0.50    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f541,f69])).
% 0.22/0.50  fof(f541,plain,(
% 0.22/0.50    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_15 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f540,f152])).
% 0.22/0.50  fof(f540,plain,(
% 0.22/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_46)),
% 0.22/0.50    inference(subsumption_resolution,[],[f539,f110])).
% 0.22/0.51  fof(f539,plain,(
% 0.22/0.51    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_46)),
% 0.22/0.51    inference(subsumption_resolution,[],[f538,f73])).
% 0.22/0.51  fof(f538,plain,(
% 0.22/0.51    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_46)),
% 0.22/0.51    inference(subsumption_resolution,[],[f537,f114])).
% 0.22/0.51  fof(f537,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_46)),
% 0.22/0.51    inference(subsumption_resolution,[],[f536,f77])).
% 0.22/0.51  fof(f536,plain,(
% 0.22/0.51    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_4 | spl6_5 | ~spl6_12 | ~spl6_46)),
% 0.22/0.51    inference(subsumption_resolution,[],[f535,f118])).
% 0.22/0.51  fof(f535,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_4 | spl6_5 | ~spl6_46)),
% 0.22/0.51    inference(subsumption_resolution,[],[f534,f81])).
% 0.22/0.51  fof(f534,plain,(
% 0.22/0.51    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_5 | ~spl6_46)),
% 0.22/0.51    inference(subsumption_resolution,[],[f500,f85])).
% 0.22/0.51  fof(f500,plain,(
% 0.22/0.51    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl6_46),
% 0.22/0.51    inference(resolution,[],[f386,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.22/0.51    inference(equality_resolution,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f387,plain,(
% 0.22/0.51    spl6_46 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f339,f151,f145,f117,f113,f109,f103,f88,f84,f80,f76,f72,f68,f385])).
% 0.22/0.51  fof(f339,plain,(
% 0.22/0.51    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f338,f77])).
% 0.22/0.51  fof(f338,plain,(
% 0.22/0.51    v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f337,f104])).
% 0.22/0.51  fof(f337,plain,(
% 0.22/0.51    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f336,f69])).
% 0.22/0.51  fof(f336,plain,(
% 0.22/0.51    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f334,f114])).
% 0.22/0.51  fof(f334,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(resolution,[],[f245,f146])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f244,f85])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f243,f110])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f242,f73])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (spl6_4 | spl6_6 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(resolution,[],[f139,f152])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ( ! [X12,X10,X11,X9] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | v1_xboole_0(X9) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | (spl6_4 | spl6_6 | ~spl6_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f138,f89])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    ( ! [X12,X10,X11,X9] : (v1_xboole_0(X9) | v1_xboole_0(sK0) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | (spl6_4 | ~spl6_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f133,f81])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X12,X10,X11,X9] : (v1_xboole_0(X9) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | ~spl6_12),
% 0.22/0.51    inference(resolution,[],[f118,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.22/0.51  fof(f371,plain,(
% 0.22/0.51    spl6_42 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f314,f151,f145,f117,f113,f109,f103,f88,f84,f80,f76,f72,f68,f369])).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f313,f77])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f312,f104])).
% 0.22/0.51  fof(f312,plain,(
% 0.22/0.51    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f311,f69])).
% 0.22/0.51  fof(f311,plain,(
% 0.22/0.51    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f309,f114])).
% 0.22/0.51  fof(f309,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(resolution,[],[f233,f146])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f232,f85])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f231,f110])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f230,f73])).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (spl6_4 | spl6_6 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(resolution,[],[f137,f152])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | v1_xboole_0(X5) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | (spl6_4 | spl6_6 | ~spl6_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f136,f89])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X6,X8,X7,X5] : (v1_xboole_0(X5) | v1_xboole_0(sK0) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | (spl6_4 | ~spl6_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f132,f81])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ( ! [X6,X8,X7,X5] : (v1_xboole_0(X5) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | ~spl6_12),
% 0.22/0.51    inference(resolution,[],[f118,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f355,plain,(
% 0.22/0.51    spl6_38 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f292,f151,f145,f117,f113,f109,f103,f88,f84,f80,f76,f72,f68,f353])).
% 0.22/0.51  fof(f292,plain,(
% 0.22/0.51    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f291,f77])).
% 0.22/0.51  fof(f291,plain,(
% 0.22/0.51    v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f290,f104])).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f289,f69])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f287,f114])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_14 | ~spl6_15)),
% 0.22/0.51    inference(resolution,[],[f220,f146])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f219,f85])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_10 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f218,f110])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f217,f73])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (spl6_4 | spl6_6 | ~spl6_12 | ~spl6_15)),
% 0.22/0.51    inference(resolution,[],[f135,f152])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | v1_xboole_0(X1) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | (spl6_4 | spl6_6 | ~spl6_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f134,f89])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | (spl6_4 | ~spl6_12)),
% 0.22/0.51    inference(subsumption_resolution,[],[f131,f81])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ( ! [X4,X2,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | ~spl6_12),
% 0.22/0.51    inference(resolution,[],[f118,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f322,plain,(
% 0.22/0.51    spl6_35 | ~spl6_20 | ~spl6_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f307,f207,f185,f320])).
% 0.22/0.51  % (20904)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    spl6_20 <=> v1_relat_1(sK4)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    spl6_24 <=> sK4 = k7_relat_1(sK4,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.51  fof(f307,plain,(
% 0.22/0.51    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | (~spl6_20 | ~spl6_24)),
% 0.22/0.51    inference(superposition,[],[f270,f208])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    sK4 = k7_relat_1(sK4,sK2) | ~spl6_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f207])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0)) ) | ~spl6_20),
% 0.22/0.51    inference(resolution,[],[f189,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),X1)) ) | ~spl6_20),
% 0.22/0.51    inference(resolution,[],[f186,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    v1_relat_1(sK4) | ~spl6_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f185])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    spl6_25 | ~spl6_16 | ~spl6_23),
% 0.22/0.51    inference(avatar_split_clause,[],[f216,f203,f171,f222])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    spl6_16 <=> v1_relat_1(sK5)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    spl6_23 <=> sK5 = k7_relat_1(sK5,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | (~spl6_16 | ~spl6_23)),
% 0.22/0.51    inference(superposition,[],[f210,f204])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    sK5 = k7_relat_1(sK5,sK3) | ~spl6_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f203])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0)) ) | ~spl6_16),
% 0.22/0.51    inference(resolution,[],[f188,f61])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X0),X1)) ) | ~spl6_16),
% 0.22/0.51    inference(resolution,[],[f172,f57])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    v1_relat_1(sK5) | ~spl6_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f171])).
% 0.22/0.51  % (20888)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    spl6_24 | ~spl6_20 | ~spl6_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f201,f195,f185,f207])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    spl6_22 <=> v4_relat_1(sK4,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    sK4 = k7_relat_1(sK4,sK2) | (~spl6_20 | ~spl6_22)),
% 0.22/0.51    inference(subsumption_resolution,[],[f200,f186])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    ~v1_relat_1(sK4) | sK4 = k7_relat_1(sK4,sK2) | ~spl6_22),
% 0.22/0.51    inference(resolution,[],[f196,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    v4_relat_1(sK4,sK2) | ~spl6_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f195])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    spl6_23 | ~spl6_16 | ~spl6_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f199,f191,f171,f203])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    spl6_21 <=> v4_relat_1(sK5,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    sK5 = k7_relat_1(sK5,sK3) | (~spl6_16 | ~spl6_21)),
% 0.22/0.51    inference(subsumption_resolution,[],[f198,f172])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    ~v1_relat_1(sK5) | sK5 = k7_relat_1(sK5,sK3) | ~spl6_21),
% 0.22/0.51    inference(resolution,[],[f192,f58])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    v4_relat_1(sK5,sK3) | ~spl6_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f191])).
% 0.22/0.51  % (20905)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    spl6_22 | ~spl6_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f162,f151,f195])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    v4_relat_1(sK4,sK2) | ~spl6_15),
% 0.22/0.51    inference(resolution,[],[f152,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    spl6_21 | ~spl6_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f154,f145,f191])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    v4_relat_1(sK5,sK3) | ~spl6_14),
% 0.22/0.51    inference(resolution,[],[f146,f62])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    spl6_20 | ~spl6_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f163,f151,f185])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    v1_relat_1(sK4) | ~spl6_15),
% 0.22/0.51    inference(resolution,[],[f152,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ~spl6_17 | ~spl6_18 | ~spl6_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f32,f181,f178,f175])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f12])).
% 0.22/0.51  % (20902)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  fof(f12,conjecture,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    spl6_16 | ~spl6_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f155,f145,f171])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    v1_relat_1(sK5) | ~spl6_14),
% 0.22/0.51    inference(resolution,[],[f146,f54])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    spl6_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f38,f151])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    spl6_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f35,f145])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    spl6_13 | ~spl6_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f106,f99,f141])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    spl6_8 <=> r1_xboole_0(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK2,sK3) | ~spl6_8),
% 0.22/0.51    inference(resolution,[],[f100,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    r1_xboole_0(sK2,sK3) | ~spl6_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f99])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl6_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f43,f117])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    spl6_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f40,f113])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl6_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f37,f109])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    v1_funct_2(sK4,sK2,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    spl6_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f34,f103])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    v1_funct_2(sK5,sK3,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl6_8 | spl6_3 | spl6_4 | ~spl6_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f97,f92,f80,f76,f99])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl6_7 <=> r1_subset_1(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    r1_xboole_0(sK2,sK3) | (spl6_3 | spl6_4 | ~spl6_7)),
% 0.22/0.51    inference(subsumption_resolution,[],[f96,f81])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | (spl6_3 | ~spl6_7)),
% 0.22/0.51    inference(subsumption_resolution,[],[f95,f77])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl6_7),
% 0.22/0.51    inference(resolution,[],[f93,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    r1_subset_1(sK2,sK3) | ~spl6_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f92])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    spl6_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f41,f92])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    r1_subset_1(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ~spl6_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f45,f88])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ~spl6_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f44,f84])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ~v1_xboole_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ~spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f42,f80])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ~v1_xboole_0(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f39,f76])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ~v1_xboole_0(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f36,f72])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    v1_funct_1(sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f33,f68])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    v1_funct_1(sK5)),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (20884)------------------------------
% 0.22/0.51  % (20884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20884)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (20884)Memory used [KB]: 6780
% 0.22/0.51  % (20884)Time elapsed: 0.072 s
% 0.22/0.51  % (20884)------------------------------
% 0.22/0.51  % (20884)------------------------------
% 0.22/0.51  % (20905)Refutation not found, incomplete strategy% (20905)------------------------------
% 0.22/0.51  % (20905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20905)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20905)Memory used [KB]: 10618
% 0.22/0.51  % (20905)Time elapsed: 0.096 s
% 0.22/0.51  % (20905)------------------------------
% 0.22/0.51  % (20905)------------------------------
% 0.22/0.51  % (20877)Success in time 0.15 s
%------------------------------------------------------------------------------
