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
% DateTime   : Thu Dec  3 13:17:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  309 ( 778 expanded)
%              Number of leaves         :   48 ( 296 expanded)
%              Depth                    :   29
%              Number of atoms          : 2233 (4094 expanded)
%              Number of equality atoms :  187 ( 465 expanded)
%              Maximal formula depth    :   26 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (22371)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f867,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f86,f90,f94,f98,f102,f106,f116,f120,f124,f128,f136,f141,f145,f170,f174,f202,f212,f216,f224,f228,f232,f236,f246,f250,f261,f274,f369,f421,f495,f592,f831,f857,f866])).

fof(f866,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f865])).

fof(f865,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f864,f273])).

fof(f273,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl6_29
  <=> k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f864,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f863,f368])).

fof(f368,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl6_36
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f863,plain,
    ( k7_relat_1(sK4,sK3) != k7_relat_1(k1_xboole_0,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_20
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f862,f329])).

fof(f329,plain,
    ( ! [X0] : k7_relat_1(sK5,k3_xboole_0(sK2,X0)) = k7_relat_1(k1_xboole_0,X0)
    | ~ spl6_17
    | ~ spl6_28 ),
    inference(superposition,[],[f218,f260])).

fof(f260,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl6_28
  <=> k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f218,plain,
    ( ! [X2,X1] : k7_relat_1(k7_relat_1(sK5,X1),X2) = k7_relat_1(sK5,k3_xboole_0(X1,X2))
    | ~ spl6_17 ),
    inference(resolution,[],[f201,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f201,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_17
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f862,plain,
    ( k7_relat_1(sK4,sK3) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | spl6_20
    | ~ spl6_21
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f861,f322])).

fof(f322,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(sK2,X0))
    | ~ spl6_21
    | ~ spl6_27 ),
    inference(superposition,[],[f219,f249])).

fof(f249,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl6_27
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f219,plain,
    ( ! [X0] : k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0))
    | ~ spl6_21 ),
    inference(resolution,[],[f215,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f215,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl6_21
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f861,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_16
    | spl6_20 ),
    inference(forward_demodulation,[],[f860,f198])).

fof(f198,plain,
    ( ! [X0] : k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl6_2
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f190,f85])).

fof(f85,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_2
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) )
    | ~ spl6_16 ),
    inference(resolution,[],[f173,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f173,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl6_16
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f860,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_12
    | ~ spl6_15
    | spl6_20 ),
    inference(forward_demodulation,[],[f859,f147])).

fof(f147,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)
    | ~ spl6_12 ),
    inference(resolution,[],[f135,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f135,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f134])).

% (22379)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f134,plain,
    ( spl6_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f859,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_15
    | spl6_20 ),
    inference(forward_demodulation,[],[f211,f186])).

fof(f186,plain,
    ( ! [X0] : k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | ~ spl6_1
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f178,f81])).

fof(f81,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_1
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK5)
        | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) )
    | ~ spl6_15 ),
    inference(resolution,[],[f169,f60])).

fof(f169,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_15
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f211,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl6_20
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f857,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_19
    | ~ spl6_21
    | ~ spl6_26
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(avatar_contradiction_clause,[],[f856])).

fof(f856,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_19
    | ~ spl6_21
    | ~ spl6_26
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f208,f808])).

fof(f808,plain,
    ( sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_26
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f807,f260])).

fof(f807,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,sK2)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_26
    | ~ spl6_27
    | ~ spl6_29
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f806,f273])).

fof(f806,plain,
    ( k7_relat_1(sK5,sK2) != k7_relat_1(sK4,sK3)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_26
    | ~ spl6_27
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f805,f286])).

fof(f286,plain,
    ( ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(X0,sK3))
    | ~ spl6_17
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f284,f245])).

fof(f245,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl6_26
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f284,plain,
    ( ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(X0,k1_relat_1(sK5)))
    | ~ spl6_17 ),
    inference(superposition,[],[f217,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f217,plain,
    ( ! [X0] : k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0))
    | ~ spl6_17 ),
    inference(resolution,[],[f201,f68])).

fof(f805,plain,
    ( k7_relat_1(sK4,sK3) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f804,f322])).

fof(f804,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f803,f198])).

fof(f803,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f802,f147])).

fof(f802,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f801,f186])).

fof(f801,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f800,f101])).

fof(f101,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f800,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK0)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f799,f494])).

fof(f494,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl6_44
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f799,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_39
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f798,f420])).

fof(f420,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl6_39
  <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f798,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f797,f169])).

fof(f797,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f796,f119])).

fof(f119,plain,
    ( v1_funct_2(sK5,sK3,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_9
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f796,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f795,f81])).

fof(f795,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f794,f173])).

fof(f794,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f793,f127])).

fof(f127,plain,
    ( v1_funct_2(sK4,sK2,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_11
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f793,plain,
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
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f792,f85])).

fof(f792,plain,
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
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f791,f135])).

fof(f791,plain,
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
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f790,f89])).

fof(f89,plain,
    ( ~ v1_xboole_0(sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_3
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f790,plain,
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
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f789,f140])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl6_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f789,plain,
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
    inference(subsumption_resolution,[],[f788,f93])).

fof(f93,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f788,plain,
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
    inference(subsumption_resolution,[],[f772,f97])).

fof(f97,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f772,plain,
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
    inference(resolution,[],[f591,f77])).

fof(f77,plain,(
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
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f591,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl6_48
  <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f208,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl6_19
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f831,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_36
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(avatar_contradiction_clause,[],[f830])).

fof(f830,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_36
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f829,f273])).

fof(f829,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_36
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f828,f368])).

fof(f828,plain,
    ( k7_relat_1(sK4,sK3) != k7_relat_1(k1_xboole_0,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_28
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f827,f329])).

fof(f827,plain,
    ( k7_relat_1(sK4,sK3) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_21
    | ~ spl6_27
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f826,f322])).

fof(f826,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f825,f198])).

fof(f825,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f824,f147])).

fof(f824,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f823,f186])).

fof(f823,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | spl6_18
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f822,f205])).

fof(f205,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl6_18
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f822,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f821,f101])).

fof(f821,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK0)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_39
    | ~ spl6_44
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f820,f494])).

fof(f820,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_39
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f819,f420])).

fof(f819,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f818,f169])).

fof(f818,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f817,f119])).

fof(f817,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f816,f81])).

fof(f816,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_16
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f815,f173])).

fof(f815,plain,
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
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f814,f127])).

fof(f814,plain,
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
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f813,f85])).

fof(f813,plain,
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
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f812,f135])).

fof(f812,plain,
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
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f811,f89])).

fof(f811,plain,
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
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f810,f140])).

fof(f810,plain,
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
    inference(subsumption_resolution,[],[f809,f93])).

fof(f809,plain,
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
    inference(subsumption_resolution,[],[f773,f97])).

fof(f773,plain,
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
    inference(resolution,[],[f591,f76])).

fof(f76,plain,(
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
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f592,plain,
    ( spl6_48
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f427,f172,f168,f139,f134,f126,f118,f100,f96,f92,f88,f84,f80,f590])).

fof(f427,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f426,f89])).

fof(f426,plain,
    ( v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f425,f119])).

fof(f425,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f424,f81])).

fof(f424,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f422,f135])).

fof(f422,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(resolution,[],[f297,f169])).

fof(f297,plain,
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
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f296,f97])).

fof(f296,plain,
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
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f295,f127])).

fof(f295,plain,
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
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f294,f85])).

fof(f294,plain,
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
    | ~ spl6_16 ),
    inference(resolution,[],[f166,f173])).

fof(f166,plain,
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
    inference(subsumption_resolution,[],[f165,f101])).

fof(f165,plain,
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
    inference(subsumption_resolution,[],[f160,f93])).

fof(f160,plain,
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
    inference(resolution,[],[f140,f56])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f495,plain,
    ( spl6_44
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f399,f172,f168,f139,f134,f126,f118,f100,f96,f92,f88,f84,f80,f493])).

fof(f399,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f398,f89])).

fof(f398,plain,
    ( v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f397,f119])).

fof(f397,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f396,f81])).

fof(f396,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f394,f135])).

fof(f394,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(resolution,[],[f282,f169])).

fof(f282,plain,
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
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f281,f97])).

fof(f281,plain,
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
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f280,f127])).

fof(f280,plain,
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
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f279,f85])).

fof(f279,plain,
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
    | ~ spl6_16 ),
    inference(resolution,[],[f164,f173])).

fof(f164,plain,
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
    inference(subsumption_resolution,[],[f163,f101])).

fof(f163,plain,
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
    inference(subsumption_resolution,[],[f159,f93])).

fof(f159,plain,
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
    inference(resolution,[],[f140,f55])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f421,plain,
    ( spl6_39
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f375,f172,f168,f139,f134,f126,f118,f100,f96,f92,f88,f84,f80,f419])).

fof(f375,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f374,f89])).

fof(f374,plain,
    ( v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f373,f119])).

fof(f373,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f372,f81])).

fof(f372,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f370,f135])).

fof(f370,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_xboole_0(sK3)
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ spl6_2
    | spl6_4
    | spl6_5
    | spl6_6
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(resolution,[],[f270,f169])).

fof(f270,plain,
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
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f269,f97])).

fof(f269,plain,
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
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f268,f127])).

fof(f268,plain,
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
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f267,f85])).

fof(f267,plain,
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
    | ~ spl6_16 ),
    inference(resolution,[],[f162,f173])).

fof(f162,plain,
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
    inference(subsumption_resolution,[],[f161,f101])).

fof(f161,plain,
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
    inference(subsumption_resolution,[],[f158,f93])).

fof(f158,plain,
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
    inference(resolution,[],[f140,f54])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f369,plain,
    ( spl6_36
    | ~ spl6_17
    | ~ spl6_26
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f354,f259,f244,f200,f367])).

fof(f354,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3)
    | ~ spl6_17
    | ~ spl6_26
    | ~ spl6_28 ),
    inference(forward_demodulation,[],[f351,f260])).

fof(f351,plain,
    ( k7_relat_1(sK5,sK2) = k7_relat_1(k1_xboole_0,sK3)
    | ~ spl6_17
    | ~ spl6_26
    | ~ spl6_28 ),
    inference(superposition,[],[f329,f286])).

fof(f274,plain,
    ( spl6_29
    | ~ spl6_14
    | ~ spl6_21
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f266,f248,f214,f143,f272])).

fof(f143,plain,
    ( spl6_14
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f266,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK3)
    | ~ spl6_14
    | ~ spl6_21
    | ~ spl6_27 ),
    inference(resolution,[],[f256,f144])).

fof(f144,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl6_21
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f254,f215])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ v1_relat_1(sK4)
        | k1_xboole_0 = k7_relat_1(sK4,X0) )
    | ~ spl6_27 ),
    inference(superposition,[],[f72,f249])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f261,plain,
    ( spl6_28
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f257,f244,f200,f122,f259])).

fof(f122,plain,
    ( spl6_10
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f257,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,sK2)
    | ~ spl6_10
    | ~ spl6_17
    | ~ spl6_26 ),
    inference(resolution,[],[f253,f123])).

fof(f123,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl6_17
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f251,f201])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK3)
        | ~ v1_relat_1(sK5)
        | k1_xboole_0 = k7_relat_1(sK5,X0) )
    | ~ spl6_26 ),
    inference(superposition,[],[f72,f245])).

fof(f250,plain,
    ( spl6_27
    | ~ spl6_21
    | ~ spl6_24
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f242,f234,f230,f214,f248])).

fof(f230,plain,
    ( spl6_24
  <=> v4_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f234,plain,
    ( spl6_25
  <=> v1_partfun1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f242,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ spl6_21
    | ~ spl6_24
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f241,f215])).

fof(f241,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_24
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f240,f231])).

fof(f231,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f230])).

fof(f240,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | sK2 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_25 ),
    inference(resolution,[],[f235,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f235,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f234])).

fof(f246,plain,
    ( spl6_26
    | ~ spl6_17
    | ~ spl6_22
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f239,f226,f222,f200,f244])).

fof(f222,plain,
    ( spl6_22
  <=> v4_relat_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f226,plain,
    ( spl6_23
  <=> v1_partfun1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f239,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ spl6_17
    | ~ spl6_22
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f238,f201])).

fof(f238,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl6_22
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f237,f223])).

fof(f223,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f222])).

fof(f237,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | sK3 = k1_relat_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl6_23 ),
    inference(resolution,[],[f227,f71])).

fof(f227,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f226])).

fof(f236,plain,
    ( spl6_25
    | ~ spl6_2
    | spl6_5
    | ~ spl6_11
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f197,f172,f126,f96,f84,f234])).

fof(f197,plain,
    ( v1_partfun1(sK4,sK2)
    | ~ spl6_2
    | spl6_5
    | ~ spl6_11
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f196,f127])).

fof(f196,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl6_2
    | spl6_5
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f195,f85])).

fof(f195,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | spl6_5
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f188,f97])).

fof(f188,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f173,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f232,plain,
    ( spl6_24
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f187,f172,f230])).

fof(f187,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f173,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f228,plain,
    ( spl6_23
    | ~ spl6_1
    | spl6_5
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f185,f168,f118,f96,f80,f226])).

fof(f185,plain,
    ( v1_partfun1(sK5,sK3)
    | ~ spl6_1
    | spl6_5
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f184,f119])).

fof(f184,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl6_1
    | spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f183,f81])).

fof(f183,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f176,f97])).

fof(f176,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ spl6_15 ),
    inference(resolution,[],[f169,f63])).

fof(f224,plain,
    ( spl6_22
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f175,f168,f222])).

fof(f175,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ spl6_15 ),
    inference(resolution,[],[f169,f73])).

fof(f216,plain,
    ( spl6_21
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f189,f172,f214])).

fof(f189,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_16 ),
    inference(resolution,[],[f173,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f212,plain,
    ( ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f40,f210,f207,f204])).

fof(f40,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f202,plain,
    ( spl6_17
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f177,f168,f200])).

fof(f177,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_15 ),
    inference(resolution,[],[f169,f62])).

fof(f174,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f46,f172])).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f170,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f43,f168])).

fof(f43,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f145,plain,
    ( spl6_14
    | spl6_3
    | spl6_4
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f132,f114,f92,f88,f143])).

fof(f114,plain,
    ( spl6_8
  <=> r1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f132,plain,
    ( r1_xboole_0(sK3,sK2)
    | spl6_3
    | spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f131,f89])).

fof(f131,plain,
    ( r1_xboole_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f130,f93])).

fof(f130,plain,
    ( v1_xboole_0(sK2)
    | r1_xboole_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ spl6_8 ),
    inference(resolution,[],[f115,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f115,plain,
    ( r1_subset_1(sK3,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f141,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f51,f139])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f136,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f48,f134])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f128,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f45,f126])).

fof(f45,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f124,plain,
    ( spl6_10
    | spl6_3
    | spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f112,f104,f92,f88,f122])).

fof(f104,plain,
    ( spl6_7
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f112,plain,
    ( r1_xboole_0(sK2,sK3)
    | spl6_3
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f111,f93])).

fof(f111,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f108,f89])).

fof(f108,plain,
    ( v1_xboole_0(sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f105,f65])).

fof(f105,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f120,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f42,f118])).

fof(f42,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f116,plain,
    ( spl6_8
    | spl6_3
    | spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f110,f104,f92,f88,f114])).

fof(f110,plain,
    ( r1_subset_1(sK3,sK2)
    | spl6_3
    | spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f109,f93])).

fof(f109,plain,
    ( v1_xboole_0(sK2)
    | r1_subset_1(sK3,sK2)
    | spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f107,f89])).

fof(f107,plain,
    ( v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | r1_subset_1(sK3,sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f105,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | r1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

fof(f106,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f49,f104])).

fof(f49,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f53,f100])).

fof(f53,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f52,f96])).

fof(f52,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f50,f92])).

fof(f50,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f90,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f47,f88])).

fof(f47,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f41,f80])).

fof(f41,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (22361)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (22366)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (22378)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (22364)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (22375)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (22369)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (22373)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (22377)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (22362)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (22367)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (22370)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (22382)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (22368)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (22365)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (22380)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (22382)Refutation not found, incomplete strategy% (22382)------------------------------
% 0.21/0.51  % (22382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22382)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22382)Memory used [KB]: 10618
% 0.21/0.51  % (22382)Time elapsed: 0.095 s
% 0.21/0.51  % (22382)------------------------------
% 0.21/0.51  % (22382)------------------------------
% 0.21/0.51  % (22363)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (22381)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (22361)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  % (22371)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f867,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f82,f86,f90,f94,f98,f102,f106,f116,f120,f124,f128,f136,f141,f145,f170,f174,f202,f212,f216,f224,f228,f232,f236,f246,f250,f261,f274,f369,f421,f495,f592,f831,f857,f866])).
% 0.21/0.52  fof(f866,plain,(
% 0.21/0.52    ~spl6_1 | ~spl6_2 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_21 | ~spl6_27 | ~spl6_28 | ~spl6_29 | ~spl6_36),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f865])).
% 0.21/0.52  fof(f865,plain,(
% 0.21/0.52    $false | (~spl6_1 | ~spl6_2 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_21 | ~spl6_27 | ~spl6_28 | ~spl6_29 | ~spl6_36)),
% 0.21/0.52    inference(subsumption_resolution,[],[f864,f273])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK4,sK3) | ~spl6_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f272])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    spl6_29 <=> k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.52  fof(f864,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relat_1(sK4,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_21 | ~spl6_27 | ~spl6_28 | ~spl6_36)),
% 0.21/0.52    inference(forward_demodulation,[],[f863,f368])).
% 0.21/0.52  fof(f368,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3) | ~spl6_36),
% 0.21/0.52    inference(avatar_component_clause,[],[f367])).
% 0.21/0.52  fof(f367,plain,(
% 0.21/0.52    spl6_36 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.52  fof(f863,plain,(
% 0.21/0.52    k7_relat_1(sK4,sK3) != k7_relat_1(k1_xboole_0,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_12 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_20 | ~spl6_21 | ~spl6_27 | ~spl6_28)),
% 0.21/0.52    inference(forward_demodulation,[],[f862,f329])).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK5,k3_xboole_0(sK2,X0)) = k7_relat_1(k1_xboole_0,X0)) ) | (~spl6_17 | ~spl6_28)),
% 0.21/0.52    inference(superposition,[],[f218,f260])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK5,sK2) | ~spl6_28),
% 0.21/0.52    inference(avatar_component_clause,[],[f259])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    spl6_28 <=> k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k7_relat_1(k7_relat_1(sK5,X1),X2) = k7_relat_1(sK5,k3_xboole_0(X1,X2))) ) | ~spl6_17),
% 0.21/0.52    inference(resolution,[],[f201,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    v1_relat_1(sK5) | ~spl6_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f200])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    spl6_17 <=> v1_relat_1(sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.52  fof(f862,plain,(
% 0.21/0.52    k7_relat_1(sK4,sK3) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_2 | ~spl6_12 | ~spl6_15 | ~spl6_16 | spl6_20 | ~spl6_21 | ~spl6_27)),
% 0.21/0.52    inference(forward_demodulation,[],[f861,f322])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(sK2,X0))) ) | (~spl6_21 | ~spl6_27)),
% 0.21/0.52    inference(superposition,[],[f219,f249])).
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    sK2 = k1_relat_1(sK4) | ~spl6_27),
% 0.21/0.52    inference(avatar_component_clause,[],[f248])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    spl6_27 <=> sK2 = k1_relat_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK4,X0) = k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0))) ) | ~spl6_21),
% 0.21/0.52    inference(resolution,[],[f215,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    v1_relat_1(sK4) | ~spl6_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f214])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    spl6_21 <=> v1_relat_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.52  fof(f861,plain,(
% 0.21/0.52    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_2 | ~spl6_12 | ~spl6_15 | ~spl6_16 | spl6_20)),
% 0.21/0.52    inference(forward_demodulation,[],[f860,f198])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) ) | (~spl6_2 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f190,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    v1_funct_1(sK4) | ~spl6_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl6_2 <=> v1_funct_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_1(sK4) | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) ) | ~spl6_16),
% 0.21/0.52    inference(resolution,[],[f173,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    spl6_16 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.52  fof(f860,plain,(
% 0.21/0.52    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_12 | ~spl6_15 | spl6_20)),
% 0.21/0.52    inference(forward_demodulation,[],[f859,f147])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3)) ) | ~spl6_12),
% 0.21/0.52    inference(resolution,[],[f135,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f134])).
% 0.21/0.52  % (22379)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl6_12 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.52  fof(f859,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_15 | spl6_20)),
% 0.21/0.52    inference(forward_demodulation,[],[f211,f186])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ( ! [X0] : (k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)) ) | (~spl6_1 | ~spl6_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f178,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    v1_funct_1(sK5) | ~spl6_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl6_1 <=> v1_funct_1(sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_1(sK5) | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)) ) | ~spl6_15),
% 0.21/0.52    inference(resolution,[],[f169,f60])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    spl6_15 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f210])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    spl6_20 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.52  fof(f857,plain,(
% 0.21/0.52    ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_19 | ~spl6_21 | ~spl6_26 | ~spl6_27 | ~spl6_28 | ~spl6_29 | ~spl6_39 | ~spl6_44 | ~spl6_48),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f856])).
% 0.21/0.52  fof(f856,plain,(
% 0.21/0.52    $false | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_19 | ~spl6_21 | ~spl6_26 | ~spl6_27 | ~spl6_28 | ~spl6_29 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f208,f808])).
% 0.21/0.52  fof(f808,plain,(
% 0.21/0.52    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_21 | ~spl6_26 | ~spl6_27 | ~spl6_28 | ~spl6_29 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f807,f260])).
% 0.21/0.52  fof(f807,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relat_1(sK5,sK2) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_21 | ~spl6_26 | ~spl6_27 | ~spl6_29 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f806,f273])).
% 0.21/0.52  fof(f806,plain,(
% 0.21/0.52    k7_relat_1(sK5,sK2) != k7_relat_1(sK4,sK3) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | ~spl6_21 | ~spl6_26 | ~spl6_27 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f805,f286])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(X0,sK3))) ) | (~spl6_17 | ~spl6_26)),
% 0.21/0.52    inference(forward_demodulation,[],[f284,f245])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    sK3 = k1_relat_1(sK5) | ~spl6_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f244])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    spl6_26 <=> sK3 = k1_relat_1(sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(X0,k1_relat_1(sK5)))) ) | ~spl6_17),
% 0.21/0.52    inference(superposition,[],[f217,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK5,X0) = k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0))) ) | ~spl6_17),
% 0.21/0.52    inference(resolution,[],[f201,f68])).
% 0.21/0.52  fof(f805,plain,(
% 0.21/0.52    k7_relat_1(sK4,sK3) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_21 | ~spl6_27 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f804,f322])).
% 0.21/0.52  fof(f804,plain,(
% 0.21/0.52    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f803,f198])).
% 0.21/0.52  fof(f803,plain,(
% 0.21/0.52    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f802,f147])).
% 0.21/0.52  fof(f802,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f801,f186])).
% 0.21/0.52  fof(f801,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f800,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ~v1_xboole_0(sK0) | spl6_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    spl6_6 <=> v1_xboole_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.52  fof(f800,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f799,f494])).
% 0.21/0.52  fof(f494,plain,(
% 0.21/0.52    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~spl6_44),
% 0.21/0.52    inference(avatar_component_clause,[],[f493])).
% 0.21/0.52  fof(f493,plain,(
% 0.21/0.52    spl6_44 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.52  fof(f799,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_39 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f798,f420])).
% 0.21/0.52  fof(f420,plain,(
% 0.21/0.52    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~spl6_39),
% 0.21/0.52    inference(avatar_component_clause,[],[f419])).
% 0.21/0.52  fof(f419,plain,(
% 0.21/0.52    spl6_39 <=> v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.52  fof(f798,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f797,f169])).
% 0.21/0.52  fof(f797,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f796,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    v1_funct_2(sK5,sK3,sK1) | ~spl6_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl6_9 <=> v1_funct_2(sK5,sK3,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.52  fof(f796,plain,(
% 0.21/0.52    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f795,f81])).
% 0.21/0.52  fof(f795,plain,(
% 0.21/0.52    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f794,f173])).
% 0.21/0.52  fof(f794,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f793,f127])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    v1_funct_2(sK4,sK2,sK1) | ~spl6_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f126])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl6_11 <=> v1_funct_2(sK4,sK2,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.52  fof(f793,plain,(
% 0.21/0.52    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_13 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f792,f85])).
% 0.21/0.52  fof(f792,plain,(
% 0.21/0.52    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_13 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f791,f135])).
% 0.21/0.52  fof(f791,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_13 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f790,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~v1_xboole_0(sK3) | spl6_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    spl6_3 <=> v1_xboole_0(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f790,plain,(
% 0.21/0.52    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_4 | spl6_5 | ~spl6_13 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f789,f140])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl6_13 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.52  fof(f789,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_4 | spl6_5 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f788,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~v1_xboole_0(sK2) | spl6_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl6_4 <=> v1_xboole_0(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.52  fof(f788,plain,(
% 0.21/0.52    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (spl6_5 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f772,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1) | spl6_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl6_5 <=> v1_xboole_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.52  fof(f772,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~spl6_48),
% 0.21/0.52    inference(resolution,[],[f591,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4) )),
% 0.21/0.52    inference(equality_resolution,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.21/0.52  fof(f591,plain,(
% 0.21/0.52    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~spl6_48),
% 0.21/0.52    inference(avatar_component_clause,[],[f590])).
% 0.21/0.52  fof(f590,plain,(
% 0.21/0.52    spl6_48 <=> m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl6_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f207])).
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    spl6_19 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.52  fof(f831,plain,(
% 0.21/0.52    ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18 | ~spl6_21 | ~spl6_27 | ~spl6_28 | ~spl6_29 | ~spl6_36 | ~spl6_39 | ~spl6_44 | ~spl6_48),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f830])).
% 0.21/0.52  fof(f830,plain,(
% 0.21/0.52    $false | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18 | ~spl6_21 | ~spl6_27 | ~spl6_28 | ~spl6_29 | ~spl6_36 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f829,f273])).
% 0.21/0.52  fof(f829,plain,(
% 0.21/0.52    k1_xboole_0 != k7_relat_1(sK4,sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18 | ~spl6_21 | ~spl6_27 | ~spl6_28 | ~spl6_36 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f828,f368])).
% 0.21/0.52  fof(f828,plain,(
% 0.21/0.52    k7_relat_1(sK4,sK3) != k7_relat_1(k1_xboole_0,sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18 | ~spl6_21 | ~spl6_27 | ~spl6_28 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f827,f329])).
% 0.21/0.52  fof(f827,plain,(
% 0.21/0.52    k7_relat_1(sK4,sK3) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_21 | ~spl6_27 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f826,f322])).
% 0.21/0.52  fof(f826,plain,(
% 0.21/0.52    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f825,f198])).
% 0.21/0.52  fof(f825,plain,(
% 0.21/0.52    k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f824,f147])).
% 0.21/0.52  fof(f824,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(forward_demodulation,[],[f823,f186])).
% 0.21/0.52  fof(f823,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | spl6_18 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f822,f205])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | spl6_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f204])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    spl6_18 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.52  fof(f822,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f821,f101])).
% 0.21/0.52  fof(f821,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_39 | ~spl6_44 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f820,f494])).
% 0.21/0.52  fof(f820,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_39 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f819,f420])).
% 0.21/0.52  fof(f819,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f818,f169])).
% 0.21/0.52  fof(f818,plain,(
% 0.21/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f817,f119])).
% 0.21/0.52  fof(f817,plain,(
% 0.21/0.52    ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f816,f81])).
% 0.21/0.52  fof(f816,plain,(
% 0.21/0.52    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_16 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f815,f173])).
% 0.21/0.52  fof(f815,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f814,f127])).
% 0.21/0.52  fof(f814,plain,(
% 0.21/0.52    ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_2 | spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_13 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f813,f85])).
% 0.21/0.52  fof(f813,plain,(
% 0.21/0.52    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_12 | ~spl6_13 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f812,f135])).
% 0.21/0.52  fof(f812,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_3 | spl6_4 | spl6_5 | ~spl6_13 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f811,f89])).
% 0.21/0.52  fof(f811,plain,(
% 0.21/0.52    v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_4 | spl6_5 | ~spl6_13 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f810,f140])).
% 0.21/0.52  fof(f810,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_4 | spl6_5 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f809,f93])).
% 0.21/0.52  fof(f809,plain,(
% 0.21/0.52    v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (spl6_5 | ~spl6_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f773,f97])).
% 0.21/0.52  fof(f773,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~spl6_48),
% 0.21/0.52    inference(resolution,[],[f591,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | v1_xboole_0(X0) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5) )),
% 0.21/0.52    inference(equality_resolution,[],[f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f592,plain,(
% 0.21/0.52    spl6_48 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f427,f172,f168,f139,f134,f126,f118,f100,f96,f92,f88,f84,f80,f590])).
% 0.21/0.52  fof(f427,plain,(
% 0.21/0.52    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f426,f89])).
% 0.21/0.52  fof(f426,plain,(
% 0.21/0.52    v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f425,f119])).
% 0.21/0.52  fof(f425,plain,(
% 0.21/0.52    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f424,f81])).
% 0.21/0.52  fof(f424,plain,(
% 0.21/0.52    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f422,f135])).
% 0.21/0.52  fof(f422,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(resolution,[],[f297,f169])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f296,f97])).
% 0.21/0.52  fof(f296,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_11 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f295,f127])).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f294,f85])).
% 0.21/0.52  fof(f294,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X0),sK1)))) ) | (spl6_4 | spl6_6 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(resolution,[],[f166,f173])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ( ! [X12,X10,X11,X9] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | v1_xboole_0(X9) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | (spl6_4 | spl6_6 | ~spl6_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f165,f101])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ( ! [X12,X10,X11,X9] : (v1_xboole_0(X9) | v1_xboole_0(sK0) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | (spl6_4 | ~spl6_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f160,f93])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ( ! [X12,X10,X11,X9] : (v1_xboole_0(X9) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X10) | ~m1_subset_1(X10,k1_zfmisc_1(sK0)) | ~v1_funct_1(X11) | ~v1_funct_2(X11,sK2,X9) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(sK2,X9))) | ~v1_funct_1(X12) | ~v1_funct_2(X12,X10,X9) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X9))) | m1_subset_1(k1_tmap_1(sK0,X9,sK2,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,X10),X9)))) ) | ~spl6_13),
% 0.21/0.52    inference(resolution,[],[f140,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.21/0.52  fof(f495,plain,(
% 0.21/0.52    spl6_44 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f399,f172,f168,f139,f134,f126,f118,f100,f96,f92,f88,f84,f80,f493])).
% 0.21/0.52  fof(f399,plain,(
% 0.21/0.52    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f398,f89])).
% 0.21/0.52  fof(f398,plain,(
% 0.21/0.52    v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f397,f119])).
% 0.21/0.52  fof(f397,plain,(
% 0.21/0.52    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f396,f81])).
% 0.21/0.52  fof(f396,plain,(
% 0.21/0.52    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f394,f135])).
% 0.21/0.52  fof(f394,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(resolution,[],[f282,f169])).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f281,f97])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_11 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f280,f127])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f279,f85])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_2(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1),k4_subset_1(sK0,sK2,X0),sK1)) ) | (spl6_4 | spl6_6 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(resolution,[],[f164,f173])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | v1_xboole_0(X5) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | (spl6_4 | spl6_6 | ~spl6_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f163,f101])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X5] : (v1_xboole_0(X5) | v1_xboole_0(sK0) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | (spl6_4 | ~spl6_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f159,f93])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ( ! [X6,X8,X7,X5] : (v1_xboole_0(X5) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK0)) | ~v1_funct_1(X7) | ~v1_funct_2(X7,sK2,X5) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK2,X5))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,X6,X5) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | v1_funct_2(k1_tmap_1(sK0,X5,sK2,X6,X7,X8),k4_subset_1(sK0,sK2,X6),X5)) ) | ~spl6_13),
% 0.21/0.52    inference(resolution,[],[f140,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f421,plain,(
% 0.21/0.52    spl6_39 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f375,f172,f168,f139,f134,f126,f118,f100,f96,f92,f88,f84,f80,f419])).
% 0.21/0.52  fof(f375,plain,(
% 0.21/0.52    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f374,f89])).
% 0.21/0.52  fof(f374,plain,(
% 0.21/0.52    v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_9 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f373,f119])).
% 0.21/0.52  fof(f373,plain,(
% 0.21/0.52    ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_1 | ~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f372,f81])).
% 0.21/0.52  fof(f372,plain,(
% 0.21/0.52    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f370,f135])).
% 0.21/0.52  fof(f370,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_xboole_0(sK3) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_13 | ~spl6_15 | ~spl6_16)),
% 0.21/0.52    inference(resolution,[],[f270,f169])).
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | v1_xboole_0(X0) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_5 | spl6_6 | ~spl6_11 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f269,f97])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_11 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f268,f127])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (~spl6_2 | spl6_4 | spl6_6 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f267,f85])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_xboole_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,X0,sK4,X1))) ) | (spl6_4 | spl6_6 | ~spl6_13 | ~spl6_16)),
% 0.21/0.52    inference(resolution,[],[f162,f173])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ( ! [X4,X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | v1_xboole_0(X1) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | (spl6_4 | spl6_6 | ~spl6_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f161,f101])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ( ! [X4,X2,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | (spl6_4 | ~spl6_13)),
% 0.21/0.52    inference(subsumption_resolution,[],[f158,f93])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ( ! [X4,X2,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(sK2) | v1_xboole_0(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,sK2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | v1_funct_1(k1_tmap_1(sK0,X1,sK2,X2,X3,X4))) ) | ~spl6_13),
% 0.21/0.52    inference(resolution,[],[f140,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    spl6_36 | ~spl6_17 | ~spl6_26 | ~spl6_28),
% 0.21/0.52    inference(avatar_split_clause,[],[f354,f259,f244,f200,f367])).
% 0.21/0.52  fof(f354,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(k1_xboole_0,sK3) | (~spl6_17 | ~spl6_26 | ~spl6_28)),
% 0.21/0.52    inference(forward_demodulation,[],[f351,f260])).
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    k7_relat_1(sK5,sK2) = k7_relat_1(k1_xboole_0,sK3) | (~spl6_17 | ~spl6_26 | ~spl6_28)),
% 0.21/0.52    inference(superposition,[],[f329,f286])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    spl6_29 | ~spl6_14 | ~spl6_21 | ~spl6_27),
% 0.21/0.52    inference(avatar_split_clause,[],[f266,f248,f214,f143,f272])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    spl6_14 <=> r1_xboole_0(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK4,sK3) | (~spl6_14 | ~spl6_21 | ~spl6_27)),
% 0.21/0.52    inference(resolution,[],[f256,f144])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    r1_xboole_0(sK3,sK2) | ~spl6_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f143])).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(X0,sK2) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | (~spl6_21 | ~spl6_27)),
% 0.21/0.52    inference(subsumption_resolution,[],[f254,f215])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~v1_relat_1(sK4) | k1_xboole_0 = k7_relat_1(sK4,X0)) ) | ~spl6_27),
% 0.21/0.52    inference(superposition,[],[f72,f249])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    spl6_28 | ~spl6_10 | ~spl6_17 | ~spl6_26),
% 0.21/0.52    inference(avatar_split_clause,[],[f257,f244,f200,f122,f259])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl6_10 <=> r1_xboole_0(sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    k1_xboole_0 = k7_relat_1(sK5,sK2) | (~spl6_10 | ~spl6_17 | ~spl6_26)),
% 0.21/0.52    inference(resolution,[],[f253,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    r1_xboole_0(sK2,sK3) | ~spl6_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(X0,sK3) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | (~spl6_17 | ~spl6_26)),
% 0.21/0.52    inference(subsumption_resolution,[],[f251,f201])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(X0,sK3) | ~v1_relat_1(sK5) | k1_xboole_0 = k7_relat_1(sK5,X0)) ) | ~spl6_26),
% 0.21/0.52    inference(superposition,[],[f72,f245])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    spl6_27 | ~spl6_21 | ~spl6_24 | ~spl6_25),
% 0.21/0.52    inference(avatar_split_clause,[],[f242,f234,f230,f214,f248])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    spl6_24 <=> v4_relat_1(sK4,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    spl6_25 <=> v1_partfun1(sK4,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    sK2 = k1_relat_1(sK4) | (~spl6_21 | ~spl6_24 | ~spl6_25)),
% 0.21/0.52    inference(subsumption_resolution,[],[f241,f215])).
% 0.21/0.52  fof(f241,plain,(
% 0.21/0.52    sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | (~spl6_24 | ~spl6_25)),
% 0.21/0.52    inference(subsumption_resolution,[],[f240,f231])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    v4_relat_1(sK4,sK2) | ~spl6_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f230])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    ~v4_relat_1(sK4,sK2) | sK2 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl6_25),
% 0.21/0.52    inference(resolution,[],[f235,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    v1_partfun1(sK4,sK2) | ~spl6_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f234])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    spl6_26 | ~spl6_17 | ~spl6_22 | ~spl6_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f239,f226,f222,f200,f244])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    spl6_22 <=> v4_relat_1(sK5,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.52  fof(f226,plain,(
% 0.21/0.52    spl6_23 <=> v1_partfun1(sK5,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    sK3 = k1_relat_1(sK5) | (~spl6_17 | ~spl6_22 | ~spl6_23)),
% 0.21/0.52    inference(subsumption_resolution,[],[f238,f201])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | (~spl6_22 | ~spl6_23)),
% 0.21/0.52    inference(subsumption_resolution,[],[f237,f223])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    v4_relat_1(sK5,sK3) | ~spl6_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f222])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    ~v4_relat_1(sK5,sK3) | sK3 = k1_relat_1(sK5) | ~v1_relat_1(sK5) | ~spl6_23),
% 0.21/0.52    inference(resolution,[],[f227,f71])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    v1_partfun1(sK5,sK3) | ~spl6_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f226])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    spl6_25 | ~spl6_2 | spl6_5 | ~spl6_11 | ~spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f197,f172,f126,f96,f84,f234])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    v1_partfun1(sK4,sK2) | (~spl6_2 | spl6_5 | ~spl6_11 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f196,f127])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | (~spl6_2 | spl6_5 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f195,f85])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | (spl6_5 | ~spl6_16)),
% 0.21/0.52    inference(subsumption_resolution,[],[f188,f97])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,sK2,sK1) | v1_partfun1(sK4,sK2) | ~spl6_16),
% 0.21/0.52    inference(resolution,[],[f173,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    spl6_24 | ~spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f187,f172,f230])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    v4_relat_1(sK4,sK2) | ~spl6_16),
% 0.21/0.52    inference(resolution,[],[f173,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    spl6_23 | ~spl6_1 | spl6_5 | ~spl6_9 | ~spl6_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f185,f168,f118,f96,f80,f226])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    v1_partfun1(sK5,sK3) | (~spl6_1 | spl6_5 | ~spl6_9 | ~spl6_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f184,f119])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | (~spl6_1 | spl6_5 | ~spl6_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f183,f81])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | (spl6_5 | ~spl6_15)),
% 0.21/0.52    inference(subsumption_resolution,[],[f176,f97])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,sK3,sK1) | v1_partfun1(sK5,sK3) | ~spl6_15),
% 0.21/0.52    inference(resolution,[],[f169,f63])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    spl6_22 | ~spl6_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f175,f168,f222])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    v4_relat_1(sK5,sK3) | ~spl6_15),
% 0.21/0.52    inference(resolution,[],[f169,f73])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    spl6_21 | ~spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f189,f172,f214])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    v1_relat_1(sK4) | ~spl6_16),
% 0.21/0.52    inference(resolution,[],[f173,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    ~spl6_18 | ~spl6_19 | ~spl6_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f210,f207,f204])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    spl6_17 | ~spl6_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f177,f168,f200])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    v1_relat_1(sK5) | ~spl6_15),
% 0.21/0.52    inference(resolution,[],[f169,f62])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    spl6_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f46,f172])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl6_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f168])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl6_14 | spl6_3 | spl6_4 | ~spl6_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f132,f114,f92,f88,f143])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    spl6_8 <=> r1_subset_1(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    r1_xboole_0(sK3,sK2) | (spl6_3 | spl6_4 | ~spl6_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f131,f89])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    r1_xboole_0(sK3,sK2) | v1_xboole_0(sK3) | (spl6_4 | ~spl6_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f130,f93])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    v1_xboole_0(sK2) | r1_xboole_0(sK3,sK2) | v1_xboole_0(sK3) | ~spl6_8),
% 0.21/0.52    inference(resolution,[],[f115,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    r1_subset_1(sK3,sK2) | ~spl6_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f114])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    spl6_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f139])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    spl6_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f48,f134])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    spl6_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f45,f126])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    v1_funct_2(sK4,sK2,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl6_10 | spl6_3 | spl6_4 | ~spl6_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f112,f104,f92,f88,f122])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl6_7 <=> r1_subset_1(sK2,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    r1_xboole_0(sK2,sK3) | (spl6_3 | spl6_4 | ~spl6_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f111,f93])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | (spl6_3 | ~spl6_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f108,f89])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    v1_xboole_0(sK3) | r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2) | ~spl6_7),
% 0.21/0.52    inference(resolution,[],[f105,f65])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    r1_subset_1(sK2,sK3) | ~spl6_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f104])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    spl6_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f118])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    v1_funct_2(sK5,sK3,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl6_8 | spl6_3 | spl6_4 | ~spl6_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f110,f104,f92,f88,f114])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    r1_subset_1(sK3,sK2) | (spl6_3 | spl6_4 | ~spl6_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f109,f93])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    v1_xboole_0(sK2) | r1_subset_1(sK3,sK2) | (spl6_3 | ~spl6_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f107,f89])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    v1_xboole_0(sK3) | v1_xboole_0(sK2) | r1_subset_1(sK3,sK2) | ~spl6_7),
% 0.21/0.52    inference(resolution,[],[f105,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | r1_subset_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) => r1_subset_1(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_subset_1)).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl6_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f49,f104])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    r1_subset_1(sK2,sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    ~spl6_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f53,f100])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ~v1_xboole_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ~spl6_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f52,f96])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ~spl6_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f50,f92])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ~v1_xboole_0(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~spl6_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f47,f88])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ~v1_xboole_0(sK3)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl6_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f44,f84])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v1_funct_1(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl6_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f80])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    v1_funct_1(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22361)------------------------------
% 0.21/0.52  % (22361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22361)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22361)Memory used [KB]: 7036
% 0.21/0.52  % (22361)Time elapsed: 0.103 s
% 0.21/0.52  % (22361)------------------------------
% 0.21/0.52  % (22361)------------------------------
% 0.21/0.52  % (22374)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (22376)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (22362)Refutation not found, incomplete strategy% (22362)------------------------------
% 0.21/0.52  % (22362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22362)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22362)Memory used [KB]: 10746
% 0.21/0.52  % (22362)Time elapsed: 0.102 s
% 0.21/0.52  % (22362)------------------------------
% 0.21/0.52  % (22362)------------------------------
% 0.21/0.53  % (22358)Success in time 0.168 s
%------------------------------------------------------------------------------
