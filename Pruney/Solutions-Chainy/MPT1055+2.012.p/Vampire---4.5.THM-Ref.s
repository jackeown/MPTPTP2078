%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:15 EST 2020

% Result     : Theorem 4.65s
% Output     : Refutation 4.65s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 405 expanded)
%              Number of leaves         :   51 ( 186 expanded)
%              Depth                    :   10
%              Number of atoms          :  710 (1918 expanded)
%              Number of equality atoms :   66 ( 107 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5519,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f165,f170,f175,f180,f197,f208,f261,f330,f347,f444,f473,f527,f538,f543,f552,f557,f578,f747,f914,f934,f990,f1217,f1243,f1249,f1736,f1834,f2309,f4176,f4188,f4246,f4270,f5404,f5518])).

fof(f5518,plain,
    ( spl6_87
    | ~ spl6_100
    | ~ spl6_131
    | ~ spl6_285 ),
    inference(avatar_contradiction_clause,[],[f5517])).

fof(f5517,plain,
    ( $false
    | spl6_87
    | ~ spl6_100
    | ~ spl6_131
    | ~ spl6_285 ),
    inference(subsumption_resolution,[],[f5516,f1139])).

fof(f1139,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl6_87 ),
    inference(avatar_component_clause,[],[f1138])).

fof(f1138,plain,
    ( spl6_87
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f5516,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_100
    | ~ spl6_131
    | ~ spl6_285 ),
    inference(forward_demodulation,[],[f5512,f1241])).

fof(f1241,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f1239])).

fof(f1239,plain,
    ( spl6_100
  <=> sK0 = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f5512,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl6_131
    | ~ spl6_285 ),
    inference(superposition,[],[f1833,f5181])).

fof(f5181,plain,
    ( ! [X1] : k10_relat_1(sK2,X1) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,X1)
    | ~ spl6_285 ),
    inference(avatar_component_clause,[],[f5180])).

fof(f5180,plain,
    ( spl6_285
  <=> ! [X1] : k10_relat_1(sK2,X1) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_285])])).

fof(f1833,plain,
    ( k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,sK1)
    | ~ spl6_131 ),
    inference(avatar_component_clause,[],[f1831])).

fof(f1831,plain,
    ( spl6_131
  <=> k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).

fof(f5404,plain,
    ( spl6_285
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f4387,f911,f5180])).

fof(f911,plain,
    ( spl6_68
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f4387,plain,
    ( ! [X1] : k10_relat_1(sK2,X1) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,X1)
    | ~ spl6_68 ),
    inference(resolution,[],[f913,f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f913,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f911])).

fof(f4270,plain,
    ( ~ spl6_10
    | ~ spl6_42
    | spl6_44
    | ~ spl6_247 ),
    inference(avatar_contradiction_clause,[],[f4255])).

fof(f4255,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_42
    | spl6_44
    | ~ spl6_247 ),
    inference(unit_resulting_resolution,[],[f207,f555,f541,f4245])).

fof(f4245,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_247 ),
    inference(avatar_component_clause,[],[f4244])).

fof(f4244,plain,
    ( spl6_247
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_247])])).

fof(f541,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl6_42
  <=> r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f555,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl6_44 ),
    inference(avatar_component_clause,[],[f554])).

fof(f554,plain,
    ( spl6_44
  <=> r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f207,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl6_10
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f4246,plain,
    ( spl6_247
    | ~ spl6_72
    | ~ spl6_87 ),
    inference(avatar_split_clause,[],[f4126,f1138,f932,f4244])).

fof(f932,plain,
    ( spl6_72
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | ~ r1_tarski(X0,k1_relat_1(sK2))
        | r1_tarski(X0,k10_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f4126,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_72
    | ~ spl6_87 ),
    inference(backward_demodulation,[],[f933,f1140])).

fof(f1140,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f1138])).

fof(f933,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f932])).

fof(f4188,plain,
    ( ~ spl6_44
    | spl6_20
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f4177,f550,f327,f554])).

fof(f327,plain,
    ( spl6_20
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f550,plain,
    ( spl6_43
  <=> ! [X7] : k8_relset_1(sK0,sK1,sK2,X7) = k10_relat_1(sK2,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f4177,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl6_20
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f328,f551])).

fof(f551,plain,
    ( ! [X7] : k8_relset_1(sK0,sK1,sK2,X7) = k10_relat_1(sK2,X7)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f550])).

fof(f328,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f327])).

fof(f4176,plain,
    ( ~ spl6_40
    | spl6_42
    | ~ spl6_44
    | ~ spl6_160 ),
    inference(avatar_contradiction_clause,[],[f4166])).

fof(f4166,plain,
    ( $false
    | ~ spl6_40
    | spl6_42
    | ~ spl6_44
    | ~ spl6_160 ),
    inference(unit_resulting_resolution,[],[f542,f526,f556,f2308])).

fof(f2308,plain,
    ( ! [X21,X19,X20] :
        ( ~ r1_tarski(k9_relat_1(sK2,X20),X21)
        | ~ r1_tarski(X19,X20)
        | r1_tarski(k9_relat_1(sK2,X19),X21) )
    | ~ spl6_160 ),
    inference(avatar_component_clause,[],[f2307])).

fof(f2307,plain,
    ( spl6_160
  <=> ! [X20,X19,X21] :
        ( ~ r1_tarski(X19,X20)
        | ~ r1_tarski(k9_relat_1(sK2,X20),X21)
        | r1_tarski(k9_relat_1(sK2,X19),X21) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_160])])).

fof(f556,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f554])).

fof(f526,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f525])).

fof(f525,plain,
    ( spl6_40
  <=> ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f542,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl6_42 ),
    inference(avatar_component_clause,[],[f540])).

fof(f2309,plain,
    ( spl6_160
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f877,f430,f2307])).

fof(f430,plain,
    ( spl6_30
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f877,plain,
    ( ! [X21,X19,X20] :
        ( ~ r1_tarski(X19,X20)
        | ~ r1_tarski(k9_relat_1(sK2,X20),X21)
        | r1_tarski(k9_relat_1(sK2,X19),X21) )
    | ~ spl6_30 ),
    inference(resolution,[],[f283,f431])).

fof(f431,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f430])).

fof(f283,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(k9_relat_1(X2,X1),X3)
      | r1_tarski(k9_relat_1(X2,X0),X3) ) ),
    inference(resolution,[],[f128,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f1834,plain,
    ( spl6_131
    | ~ spl6_36
    | spl6_99
    | ~ spl6_123 ),
    inference(avatar_split_clause,[],[f1740,f1734,f1214,f470,f1831])).

fof(f470,plain,
    ( spl6_36
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f1214,plain,
    ( spl6_99
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f1734,plain,
    ( spl6_123
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f1740,plain,
    ( k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,sK1)
    | ~ spl6_36
    | spl6_99
    | ~ spl6_123 ),
    inference(subsumption_resolution,[],[f1738,f1215])).

fof(f1215,plain,
    ( k1_xboole_0 != sK1
    | spl6_99 ),
    inference(avatar_component_clause,[],[f1214])).

fof(f1738,plain,
    ( k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,sK1)
    | k1_xboole_0 = sK1
    | ~ spl6_36
    | ~ spl6_123 ),
    inference(resolution,[],[f1735,f472])).

fof(f472,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f470])).

fof(f1735,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_123 ),
    inference(avatar_component_clause,[],[f1734])).

fof(f1736,plain,
    ( spl6_123
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_59
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f1001,f988,f745,f430,f162,f1734])).

fof(f162,plain,
    ( spl6_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f745,plain,
    ( spl6_59
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f988,plain,
    ( spl6_74
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0)
        | k8_relset_1(X1,X0,sK2,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f1001,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_59
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f1000,f746])).

fof(f746,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) )
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f745])).

fof(f1000,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
        | k1_xboole_0 = X0
        | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl6_3
    | ~ spl6_30
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f999,f431])).

fof(f999,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
        | k1_xboole_0 = X0
        | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_3
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f997,f164])).

fof(f164,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f162])).

fof(f997,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
        | k1_xboole_0 = X0
        | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_74 ),
    inference(resolution,[],[f989,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f989,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k1_xboole_0 = X0
        | k8_relset_1(X1,X0,sK2,X0) = X1 )
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f988])).

fof(f1249,plain,
    ( spl6_100
    | ~ spl6_43
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f1219,f1210,f550,f1239])).

fof(f1210,plain,
    ( spl6_98
  <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f1219,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl6_43
    | ~ spl6_98 ),
    inference(superposition,[],[f551,f1212])).

fof(f1212,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f1210])).

fof(f1243,plain,
    ( k1_xboole_0 != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1217,plain,
    ( spl6_98
    | spl6_99
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f998,f988,f194,f172,f1214,f1210])).

fof(f172,plain,
    ( spl6_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f194,plain,
    ( spl6_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f998,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f996,f196])).

fof(f196,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f996,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl6_5
    | ~ spl6_74 ),
    inference(resolution,[],[f989,f174])).

fof(f174,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f990,plain,
    ( spl6_74
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f428,f162,f988])).

fof(f428,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0)
        | k8_relset_1(X1,X0,sK2,X0) = X1 )
    | ~ spl6_3 ),
    inference(resolution,[],[f137,f164])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f934,plain,
    ( spl6_72
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f923,f430,f162,f932])).

fof(f923,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | ~ r1_tarski(X0,k1_relat_1(sK2))
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f417,f431])).

fof(f417,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | ~ r1_tarski(X0,k1_relat_1(sK2))
        | r1_tarski(X0,k10_relat_1(sK2,X1))
        | ~ v1_relat_1(sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f136,f164])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f914,plain,
    ( spl6_68
    | ~ spl6_36
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f752,f745,f470,f911])).

fof(f752,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl6_36
    | ~ spl6_59 ),
    inference(resolution,[],[f746,f472])).

fof(f747,plain,
    ( spl6_59
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f723,f430,f162,f745])).

fof(f723,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) )
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f357,f431])).

fof(f357,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
        | ~ v1_relat_1(sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f119,f164])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f578,plain,
    ( spl6_42
    | ~ spl6_19
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f575,f536,f323,f540])).

fof(f323,plain,
    ( spl6_19
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f536,plain,
    ( spl6_41
  <=> ! [X7] : k7_relset_1(sK0,sK1,sK2,X7) = k9_relat_1(sK2,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f575,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_19
    | ~ spl6_41 ),
    inference(backward_demodulation,[],[f325,f537])).

fof(f537,plain,
    ( ! [X7] : k7_relset_1(sK0,sK1,sK2,X7) = k9_relat_1(sK2,X7)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f536])).

fof(f325,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f323])).

fof(f557,plain,
    ( spl6_44
    | ~ spl6_9
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f548,f327,f194,f554])).

fof(f548,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_9
    | ~ spl6_20 ),
    inference(backward_demodulation,[],[f329,f375])).

fof(f375,plain,
    ( ! [X7] : k8_relset_1(sK0,sK1,sK2,X7) = k10_relat_1(sK2,X7)
    | ~ spl6_9 ),
    inference(resolution,[],[f142,f196])).

fof(f329,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f327])).

fof(f552,plain,
    ( spl6_43
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f375,f194,f550])).

fof(f543,plain,
    ( ~ spl6_42
    | ~ spl6_9
    | spl6_19 ),
    inference(avatar_split_clause,[],[f534,f323,f194,f540])).

fof(f534,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_9
    | spl6_19 ),
    inference(backward_demodulation,[],[f324,f361])).

fof(f361,plain,
    ( ! [X7] : k7_relset_1(sK0,sK1,sK2,X7) = k9_relat_1(sK2,X7)
    | ~ spl6_9 ),
    inference(resolution,[],[f141,f196])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f324,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f323])).

fof(f538,plain,
    ( spl6_41
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f361,f194,f536])).

fof(f527,plain,
    ( spl6_40
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f523,f430,f162,f525])).

fof(f523,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ spl6_3
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f272,f431])).

fof(f272,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f116,f164])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f473,plain,
    ( spl6_36
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f466,f430,f258,f470])).

fof(f258,plain,
    ( spl6_14
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f466,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f264,f431])).

fof(f264,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(resolution,[],[f260,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f260,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f258])).

fof(f444,plain,
    ( ~ spl6_9
    | spl6_30 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | ~ spl6_9
    | spl6_30 ),
    inference(unit_resulting_resolution,[],[f103,f196,f432,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f432,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f430])).

fof(f103,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f347,plain,
    ( ~ spl6_19
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f341,f327,f323])).

fof(f341,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f97,f329])).

fof(f97,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,
    ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
      | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f75,f80,f79,f78,f77,f76])).

fof(f76,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                          | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                        & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                    & m1_subset_1(X3,k1_zfmisc_1(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                      | ~ r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                    & ( r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4))
                      | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4) )
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
            & v1_funct_2(X2,sK0,X1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                    | ~ r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                  & ( r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                    | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                  & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X2,sK0,sK1)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                  | ~ r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                & ( r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4))
                  | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4) )
                & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X2,sK0,sK1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
                | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
              & ( r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
                | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
              & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
              | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
            & ( r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4))
              | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4) )
            & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( ? [X4] :
          ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
            | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
          & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
            | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,
    ( ? [X4] :
        ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
          | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
        & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4))
          | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
        | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
      & ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
        | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | ~ r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & ( r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))
                        | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(X1))
                       => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                        <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

fof(f330,plain,
    ( spl6_19
    | spl6_20 ),
    inference(avatar_split_clause,[],[f96,f327,f323])).

fof(f96,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f81])).

fof(f261,plain,
    ( spl6_14
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f247,f194,f258])).

fof(f247,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl6_9 ),
    inference(resolution,[],[f133,f196])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f208,plain,
    ( spl6_10
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f201,f177,f205])).

fof(f177,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f201,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f123,f179])).

fof(f179,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f177])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f197,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f93,f194])).

fof(f93,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f81])).

fof(f180,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f94,f177])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f81])).

fof(f175,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f92,f172])).

fof(f92,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f81])).

fof(f170,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f98,f167])).

fof(f167,plain,
    ( spl6_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f98,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f165,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f91,f162])).

fof(f91,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

fof(f160,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f90,f157])).

fof(f157,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f90,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:15:07 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.50  % (11568)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (11567)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (11566)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (11564)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11572)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (11584)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (11574)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (11576)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (11583)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (11575)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (11573)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (11582)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (11588)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (11578)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (11569)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (11586)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (11563)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (11570)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (11565)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (11579)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (11585)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.55  % (11577)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (11587)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (11571)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (11580)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.57  % (11581)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 4.20/0.92  % (11576)Time limit reached!
% 4.20/0.92  % (11576)------------------------------
% 4.20/0.92  % (11576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.20/0.92  % (11576)Termination reason: Time limit
% 4.20/0.92  
% 4.20/0.92  % (11576)Memory used [KB]: 10106
% 4.20/0.92  % (11576)Time elapsed: 0.508 s
% 4.20/0.92  % (11576)------------------------------
% 4.20/0.92  % (11576)------------------------------
% 4.20/0.92  % (11577)Time limit reached!
% 4.20/0.92  % (11577)------------------------------
% 4.20/0.92  % (11577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.20/0.92  % (11577)Termination reason: Time limit
% 4.20/0.92  
% 4.20/0.92  % (11577)Memory used [KB]: 7164
% 4.20/0.92  % (11577)Time elapsed: 0.510 s
% 4.20/0.92  % (11577)------------------------------
% 4.20/0.92  % (11577)------------------------------
% 4.20/0.95  % (11563)Time limit reached!
% 4.20/0.95  % (11563)------------------------------
% 4.20/0.95  % (11563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.20/0.95  % (11563)Termination reason: Time limit
% 4.20/0.95  % (11563)Termination phase: Saturation
% 4.20/0.95  
% 4.20/0.95  % (11563)Memory used [KB]: 16375
% 4.20/0.95  % (11563)Time elapsed: 0.500 s
% 4.20/0.95  % (11563)------------------------------
% 4.20/0.95  % (11563)------------------------------
% 4.65/0.98  % (11565)Refutation found. Thanks to Tanya!
% 4.65/0.98  % SZS status Theorem for theBenchmark
% 4.65/0.98  % SZS output start Proof for theBenchmark
% 4.65/0.98  fof(f5519,plain,(
% 4.65/0.98    $false),
% 4.65/0.98    inference(avatar_sat_refutation,[],[f160,f165,f170,f175,f180,f197,f208,f261,f330,f347,f444,f473,f527,f538,f543,f552,f557,f578,f747,f914,f934,f990,f1217,f1243,f1249,f1736,f1834,f2309,f4176,f4188,f4246,f4270,f5404,f5518])).
% 4.65/0.98  fof(f5518,plain,(
% 4.65/0.98    spl6_87 | ~spl6_100 | ~spl6_131 | ~spl6_285),
% 4.65/0.98    inference(avatar_contradiction_clause,[],[f5517])).
% 4.65/0.98  fof(f5517,plain,(
% 4.65/0.98    $false | (spl6_87 | ~spl6_100 | ~spl6_131 | ~spl6_285)),
% 4.65/0.98    inference(subsumption_resolution,[],[f5516,f1139])).
% 4.65/0.98  fof(f1139,plain,(
% 4.65/0.98    sK0 != k1_relat_1(sK2) | spl6_87),
% 4.65/0.98    inference(avatar_component_clause,[],[f1138])).
% 4.65/0.98  fof(f1138,plain,(
% 4.65/0.98    spl6_87 <=> sK0 = k1_relat_1(sK2)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).
% 4.65/0.98  fof(f5516,plain,(
% 4.65/0.98    sK0 = k1_relat_1(sK2) | (~spl6_100 | ~spl6_131 | ~spl6_285)),
% 4.65/0.98    inference(forward_demodulation,[],[f5512,f1241])).
% 4.65/0.98  fof(f1241,plain,(
% 4.65/0.98    sK0 = k10_relat_1(sK2,sK1) | ~spl6_100),
% 4.65/0.98    inference(avatar_component_clause,[],[f1239])).
% 4.65/0.98  fof(f1239,plain,(
% 4.65/0.98    spl6_100 <=> sK0 = k10_relat_1(sK2,sK1)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).
% 4.65/0.98  fof(f5512,plain,(
% 4.65/0.98    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | (~spl6_131 | ~spl6_285)),
% 4.65/0.98    inference(superposition,[],[f1833,f5181])).
% 4.65/0.98  fof(f5181,plain,(
% 4.65/0.98    ( ! [X1] : (k10_relat_1(sK2,X1) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,X1)) ) | ~spl6_285),
% 4.65/0.98    inference(avatar_component_clause,[],[f5180])).
% 4.65/0.98  fof(f5180,plain,(
% 4.65/0.98    spl6_285 <=> ! [X1] : k10_relat_1(sK2,X1) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,X1)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_285])])).
% 4.65/0.98  fof(f1833,plain,(
% 4.65/0.98    k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,sK1) | ~spl6_131),
% 4.65/0.98    inference(avatar_component_clause,[],[f1831])).
% 4.65/0.98  fof(f1831,plain,(
% 4.65/0.98    spl6_131 <=> k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,sK1)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).
% 4.65/0.98  fof(f5404,plain,(
% 4.65/0.98    spl6_285 | ~spl6_68),
% 4.65/0.98    inference(avatar_split_clause,[],[f4387,f911,f5180])).
% 4.65/0.98  fof(f911,plain,(
% 4.65/0.98    spl6_68 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 4.65/0.98  fof(f4387,plain,(
% 4.65/0.98    ( ! [X1] : (k10_relat_1(sK2,X1) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,X1)) ) | ~spl6_68),
% 4.65/0.98    inference(resolution,[],[f913,f142])).
% 4.65/0.98  fof(f142,plain,(
% 4.65/0.98    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 4.65/0.98    inference(cnf_transformation,[],[f71])).
% 4.65/0.98  fof(f71,plain,(
% 4.65/0.98    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.65/0.98    inference(ennf_transformation,[],[f26])).
% 4.65/0.98  fof(f26,axiom,(
% 4.65/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 4.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 4.65/0.98  fof(f913,plain,(
% 4.65/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl6_68),
% 4.65/0.98    inference(avatar_component_clause,[],[f911])).
% 4.65/0.98  fof(f4270,plain,(
% 4.65/0.98    ~spl6_10 | ~spl6_42 | spl6_44 | ~spl6_247),
% 4.65/0.98    inference(avatar_contradiction_clause,[],[f4255])).
% 4.65/0.98  fof(f4255,plain,(
% 4.65/0.98    $false | (~spl6_10 | ~spl6_42 | spl6_44 | ~spl6_247)),
% 4.65/0.98    inference(unit_resulting_resolution,[],[f207,f555,f541,f4245])).
% 4.65/0.98  fof(f4245,plain,(
% 4.65/0.98    ( ! [X0,X1] : (~r1_tarski(X0,sK0) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | ~spl6_247),
% 4.65/0.98    inference(avatar_component_clause,[],[f4244])).
% 4.65/0.98  fof(f4244,plain,(
% 4.65/0.98    spl6_247 <=> ! [X1,X0] : (~r1_tarski(X0,sK0) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1)))),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_247])])).
% 4.65/0.98  fof(f541,plain,(
% 4.65/0.98    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl6_42),
% 4.65/0.98    inference(avatar_component_clause,[],[f540])).
% 4.65/0.98  fof(f540,plain,(
% 4.65/0.98    spl6_42 <=> r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 4.65/0.98  fof(f555,plain,(
% 4.65/0.98    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl6_44),
% 4.65/0.98    inference(avatar_component_clause,[],[f554])).
% 4.65/0.98  fof(f554,plain,(
% 4.65/0.98    spl6_44 <=> r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 4.65/0.98  fof(f207,plain,(
% 4.65/0.98    r1_tarski(sK3,sK0) | ~spl6_10),
% 4.65/0.98    inference(avatar_component_clause,[],[f205])).
% 4.65/0.98  fof(f205,plain,(
% 4.65/0.98    spl6_10 <=> r1_tarski(sK3,sK0)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 4.65/0.98  fof(f4246,plain,(
% 4.65/0.98    spl6_247 | ~spl6_72 | ~spl6_87),
% 4.65/0.98    inference(avatar_split_clause,[],[f4126,f1138,f932,f4244])).
% 4.65/0.98  fof(f932,plain,(
% 4.65/0.98    spl6_72 <=> ! [X1,X0] : (~r1_tarski(k9_relat_1(sK2,X0),X1) | ~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,X1)))),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 4.65/0.98  fof(f4126,plain,(
% 4.65/0.98    ( ! [X0,X1] : (~r1_tarski(X0,sK0) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | (~spl6_72 | ~spl6_87)),
% 4.65/0.98    inference(backward_demodulation,[],[f933,f1140])).
% 4.65/0.98  fof(f1140,plain,(
% 4.65/0.98    sK0 = k1_relat_1(sK2) | ~spl6_87),
% 4.65/0.98    inference(avatar_component_clause,[],[f1138])).
% 4.65/0.98  fof(f933,plain,(
% 4.65/0.98    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | ~spl6_72),
% 4.65/0.98    inference(avatar_component_clause,[],[f932])).
% 4.65/0.98  fof(f4188,plain,(
% 4.65/0.98    ~spl6_44 | spl6_20 | ~spl6_43),
% 4.65/0.98    inference(avatar_split_clause,[],[f4177,f550,f327,f554])).
% 4.65/0.98  fof(f327,plain,(
% 4.65/0.98    spl6_20 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 4.65/0.98  fof(f550,plain,(
% 4.65/0.98    spl6_43 <=> ! [X7] : k8_relset_1(sK0,sK1,sK2,X7) = k10_relat_1(sK2,X7)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 4.65/0.98  fof(f4177,plain,(
% 4.65/0.98    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (spl6_20 | ~spl6_43)),
% 4.65/0.98    inference(forward_demodulation,[],[f328,f551])).
% 4.65/0.98  fof(f551,plain,(
% 4.65/0.98    ( ! [X7] : (k8_relset_1(sK0,sK1,sK2,X7) = k10_relat_1(sK2,X7)) ) | ~spl6_43),
% 4.65/0.98    inference(avatar_component_clause,[],[f550])).
% 4.65/0.98  fof(f328,plain,(
% 4.65/0.98    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl6_20),
% 4.65/0.98    inference(avatar_component_clause,[],[f327])).
% 4.65/0.98  fof(f4176,plain,(
% 4.65/0.98    ~spl6_40 | spl6_42 | ~spl6_44 | ~spl6_160),
% 4.65/0.98    inference(avatar_contradiction_clause,[],[f4166])).
% 4.65/0.98  fof(f4166,plain,(
% 4.65/0.98    $false | (~spl6_40 | spl6_42 | ~spl6_44 | ~spl6_160)),
% 4.65/0.98    inference(unit_resulting_resolution,[],[f542,f526,f556,f2308])).
% 4.65/0.98  fof(f2308,plain,(
% 4.65/0.98    ( ! [X21,X19,X20] : (~r1_tarski(k9_relat_1(sK2,X20),X21) | ~r1_tarski(X19,X20) | r1_tarski(k9_relat_1(sK2,X19),X21)) ) | ~spl6_160),
% 4.65/0.98    inference(avatar_component_clause,[],[f2307])).
% 4.65/0.98  fof(f2307,plain,(
% 4.65/0.98    spl6_160 <=> ! [X20,X19,X21] : (~r1_tarski(X19,X20) | ~r1_tarski(k9_relat_1(sK2,X20),X21) | r1_tarski(k9_relat_1(sK2,X19),X21))),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_160])])).
% 4.65/0.98  fof(f556,plain,(
% 4.65/0.98    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl6_44),
% 4.65/0.98    inference(avatar_component_clause,[],[f554])).
% 4.65/0.98  fof(f526,plain,(
% 4.65/0.98    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) ) | ~spl6_40),
% 4.65/0.98    inference(avatar_component_clause,[],[f525])).
% 4.65/0.98  fof(f525,plain,(
% 4.65/0.98    spl6_40 <=> ! [X0] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 4.65/0.98  fof(f542,plain,(
% 4.65/0.98    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl6_42),
% 4.65/0.98    inference(avatar_component_clause,[],[f540])).
% 4.65/0.98  fof(f2309,plain,(
% 4.65/0.98    spl6_160 | ~spl6_30),
% 4.65/0.98    inference(avatar_split_clause,[],[f877,f430,f2307])).
% 4.65/0.98  fof(f430,plain,(
% 4.65/0.98    spl6_30 <=> v1_relat_1(sK2)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 4.65/0.98  fof(f877,plain,(
% 4.65/0.98    ( ! [X21,X19,X20] : (~r1_tarski(X19,X20) | ~r1_tarski(k9_relat_1(sK2,X20),X21) | r1_tarski(k9_relat_1(sK2,X19),X21)) ) | ~spl6_30),
% 4.65/0.98    inference(resolution,[],[f283,f431])).
% 4.65/0.98  fof(f431,plain,(
% 4.65/0.98    v1_relat_1(sK2) | ~spl6_30),
% 4.65/0.98    inference(avatar_component_clause,[],[f430])).
% 4.65/0.98  fof(f283,plain,(
% 4.65/0.98    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~r1_tarski(k9_relat_1(X2,X1),X3) | r1_tarski(k9_relat_1(X2,X0),X3)) )),
% 4.65/0.98    inference(resolution,[],[f128,f140])).
% 4.65/0.98  fof(f140,plain,(
% 4.65/0.98    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 4.65/0.98    inference(cnf_transformation,[],[f69])).
% 4.65/0.98  fof(f69,plain,(
% 4.65/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 4.65/0.98    inference(flattening,[],[f68])).
% 4.65/0.98  fof(f68,plain,(
% 4.65/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.65/0.98    inference(ennf_transformation,[],[f3])).
% 4.65/0.98  fof(f3,axiom,(
% 4.65/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 4.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 4.65/0.98  fof(f128,plain,(
% 4.65/0.98    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 4.65/0.98    inference(cnf_transformation,[],[f54])).
% 4.65/0.98  fof(f54,plain,(
% 4.65/0.98    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 4.65/0.98    inference(flattening,[],[f53])).
% 4.65/0.98  fof(f53,plain,(
% 4.65/0.98    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 4.65/0.98    inference(ennf_transformation,[],[f18])).
% 4.65/0.98  fof(f18,axiom,(
% 4.65/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 4.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 4.65/0.98  fof(f1834,plain,(
% 4.65/0.98    spl6_131 | ~spl6_36 | spl6_99 | ~spl6_123),
% 4.65/0.98    inference(avatar_split_clause,[],[f1740,f1734,f1214,f470,f1831])).
% 4.65/0.98  fof(f470,plain,(
% 4.65/0.98    spl6_36 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 4.65/0.98  fof(f1214,plain,(
% 4.65/0.98    spl6_99 <=> k1_xboole_0 = sK1),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).
% 4.65/0.98  fof(f1734,plain,(
% 4.65/0.98    spl6_123 <=> ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0) | ~r1_tarski(k2_relat_1(sK2),X0))),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).
% 4.65/0.98  fof(f1740,plain,(
% 4.65/0.98    k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,sK1) | (~spl6_36 | spl6_99 | ~spl6_123)),
% 4.65/0.98    inference(subsumption_resolution,[],[f1738,f1215])).
% 4.65/0.98  fof(f1215,plain,(
% 4.65/0.98    k1_xboole_0 != sK1 | spl6_99),
% 4.65/0.98    inference(avatar_component_clause,[],[f1214])).
% 4.65/0.98  fof(f1738,plain,(
% 4.65/0.98    k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),sK1,sK2,sK1) | k1_xboole_0 = sK1 | (~spl6_36 | ~spl6_123)),
% 4.65/0.98    inference(resolution,[],[f1735,f472])).
% 4.65/0.98  fof(f472,plain,(
% 4.65/0.98    r1_tarski(k2_relat_1(sK2),sK1) | ~spl6_36),
% 4.65/0.98    inference(avatar_component_clause,[],[f470])).
% 4.65/0.98  fof(f1735,plain,(
% 4.65/0.98    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0) | k1_xboole_0 = X0) ) | ~spl6_123),
% 4.65/0.98    inference(avatar_component_clause,[],[f1734])).
% 4.65/0.98  fof(f1736,plain,(
% 4.65/0.98    spl6_123 | ~spl6_3 | ~spl6_30 | ~spl6_59 | ~spl6_74),
% 4.65/0.98    inference(avatar_split_clause,[],[f1001,f988,f745,f430,f162,f1734])).
% 4.65/0.98  fof(f162,plain,(
% 4.65/0.98    spl6_3 <=> v1_funct_1(sK2)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 4.65/0.98  fof(f745,plain,(
% 4.65/0.98    spl6_59 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))))),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 4.65/0.98  fof(f988,plain,(
% 4.65/0.98    spl6_74 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | k8_relset_1(X1,X0,sK2,X0) = X1)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 4.65/0.98  fof(f1001,plain,(
% 4.65/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0) | ~r1_tarski(k2_relat_1(sK2),X0)) ) | (~spl6_3 | ~spl6_30 | ~spl6_59 | ~spl6_74)),
% 4.65/0.98    inference(subsumption_resolution,[],[f1000,f746])).
% 4.65/0.98  fof(f746,plain,(
% 4.65/0.98    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))) ) | ~spl6_59),
% 4.65/0.98    inference(avatar_component_clause,[],[f745])).
% 4.65/0.98  fof(f1000,plain,(
% 4.65/0.98    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) | k1_xboole_0 = X0 | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0) | ~r1_tarski(k2_relat_1(sK2),X0)) ) | (~spl6_3 | ~spl6_30 | ~spl6_74)),
% 4.65/0.98    inference(subsumption_resolution,[],[f999,f431])).
% 4.65/0.98  fof(f999,plain,(
% 4.65/0.98    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) | k1_xboole_0 = X0 | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_relat_1(sK2)) ) | (~spl6_3 | ~spl6_74)),
% 4.65/0.98    inference(subsumption_resolution,[],[f997,f164])).
% 4.65/0.98  fof(f164,plain,(
% 4.65/0.98    v1_funct_1(sK2) | ~spl6_3),
% 4.65/0.98    inference(avatar_component_clause,[],[f162])).
% 4.65/0.98  fof(f997,plain,(
% 4.65/0.98    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) | k1_xboole_0 = X0 | k1_relat_1(sK2) = k8_relset_1(k1_relat_1(sK2),X0,sK2,X0) | ~r1_tarski(k2_relat_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl6_74),
% 4.65/0.98    inference(resolution,[],[f989,f118])).
% 4.65/0.98  fof(f118,plain,(
% 4.65/0.98    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.65/0.98    inference(cnf_transformation,[],[f52])).
% 4.65/0.98  fof(f52,plain,(
% 4.65/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.65/0.98    inference(flattening,[],[f51])).
% 4.65/0.98  fof(f51,plain,(
% 4.65/0.98    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.65/0.98    inference(ennf_transformation,[],[f32])).
% 4.65/0.98  fof(f32,axiom,(
% 4.65/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 4.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 4.65/0.98  fof(f989,plain,(
% 4.65/0.98    ( ! [X0,X1] : (~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_xboole_0 = X0 | k8_relset_1(X1,X0,sK2,X0) = X1) ) | ~spl6_74),
% 4.65/0.98    inference(avatar_component_clause,[],[f988])).
% 4.65/0.98  fof(f1249,plain,(
% 4.65/0.98    spl6_100 | ~spl6_43 | ~spl6_98),
% 4.65/0.98    inference(avatar_split_clause,[],[f1219,f1210,f550,f1239])).
% 4.65/0.98  fof(f1210,plain,(
% 4.65/0.98    spl6_98 <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 4.65/0.98  fof(f1219,plain,(
% 4.65/0.98    sK0 = k10_relat_1(sK2,sK1) | (~spl6_43 | ~spl6_98)),
% 4.65/0.98    inference(superposition,[],[f551,f1212])).
% 4.65/0.98  fof(f1212,plain,(
% 4.65/0.98    sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | ~spl6_98),
% 4.65/0.98    inference(avatar_component_clause,[],[f1210])).
% 4.65/0.98  fof(f1243,plain,(
% 4.65/0.98    k1_xboole_0 != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0)),
% 4.65/0.98    introduced(theory_tautology_sat_conflict,[])).
% 4.65/0.98  fof(f1217,plain,(
% 4.65/0.98    spl6_98 | spl6_99 | ~spl6_5 | ~spl6_9 | ~spl6_74),
% 4.65/0.98    inference(avatar_split_clause,[],[f998,f988,f194,f172,f1214,f1210])).
% 4.65/0.98  fof(f172,plain,(
% 4.65/0.98    spl6_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 4.65/0.98  fof(f194,plain,(
% 4.65/0.98    spl6_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 4.65/0.98  fof(f998,plain,(
% 4.65/0.98    k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl6_5 | ~spl6_9 | ~spl6_74)),
% 4.65/0.98    inference(subsumption_resolution,[],[f996,f196])).
% 4.65/0.98  fof(f196,plain,(
% 4.65/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_9),
% 4.65/0.98    inference(avatar_component_clause,[],[f194])).
% 4.65/0.98  fof(f996,plain,(
% 4.65/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl6_5 | ~spl6_74)),
% 4.65/0.98    inference(resolution,[],[f989,f174])).
% 4.65/0.98  fof(f174,plain,(
% 4.65/0.98    v1_funct_2(sK2,sK0,sK1) | ~spl6_5),
% 4.65/0.98    inference(avatar_component_clause,[],[f172])).
% 4.65/0.98  fof(f990,plain,(
% 4.65/0.98    spl6_74 | ~spl6_3),
% 4.65/0.98    inference(avatar_split_clause,[],[f428,f162,f988])).
% 4.65/0.98  fof(f428,plain,(
% 4.65/0.98    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | k8_relset_1(X1,X0,sK2,X0) = X1) ) | ~spl6_3),
% 4.65/0.98    inference(resolution,[],[f137,f164])).
% 4.65/0.98  fof(f137,plain,(
% 4.65/0.98    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 4.65/0.98    inference(cnf_transformation,[],[f65])).
% 4.65/0.98  fof(f65,plain,(
% 4.65/0.98    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 4.65/0.98    inference(flattening,[],[f64])).
% 4.65/0.98  fof(f64,plain,(
% 4.65/0.98    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 4.65/0.98    inference(ennf_transformation,[],[f31])).
% 4.65/0.98  fof(f31,axiom,(
% 4.65/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 4.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 4.65/0.98  fof(f934,plain,(
% 4.65/0.98    spl6_72 | ~spl6_3 | ~spl6_30),
% 4.65/0.98    inference(avatar_split_clause,[],[f923,f430,f162,f932])).
% 4.65/0.98  fof(f923,plain,(
% 4.65/0.98    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK2,X0),X1) | ~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | (~spl6_3 | ~spl6_30)),
% 4.65/0.98    inference(subsumption_resolution,[],[f417,f431])).
% 4.65/0.98  fof(f417,plain,(
% 4.65/0.98    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK2,X0),X1) | ~r1_tarski(X0,k1_relat_1(sK2)) | r1_tarski(X0,k10_relat_1(sK2,X1)) | ~v1_relat_1(sK2)) ) | ~spl6_3),
% 4.65/0.98    inference(resolution,[],[f136,f164])).
% 4.65/0.98  fof(f136,plain,(
% 4.65/0.98    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | r1_tarski(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.65/0.98    inference(cnf_transformation,[],[f63])).
% 4.65/0.98  fof(f63,plain,(
% 4.65/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.65/0.98    inference(flattening,[],[f62])).
% 4.65/0.98  fof(f62,plain,(
% 4.65/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.65/0.98    inference(ennf_transformation,[],[f21])).
% 4.65/0.98  fof(f21,axiom,(
% 4.65/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 4.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 4.65/0.98  fof(f914,plain,(
% 4.65/0.98    spl6_68 | ~spl6_36 | ~spl6_59),
% 4.65/0.98    inference(avatar_split_clause,[],[f752,f745,f470,f911])).
% 4.65/0.98  fof(f752,plain,(
% 4.65/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl6_36 | ~spl6_59)),
% 4.65/0.98    inference(resolution,[],[f746,f472])).
% 4.65/0.98  fof(f747,plain,(
% 4.65/0.98    spl6_59 | ~spl6_3 | ~spl6_30),
% 4.65/0.98    inference(avatar_split_clause,[],[f723,f430,f162,f745])).
% 4.65/0.98  fof(f723,plain,(
% 4.65/0.98    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))) ) | (~spl6_3 | ~spl6_30)),
% 4.65/0.98    inference(subsumption_resolution,[],[f357,f431])).
% 4.65/0.98  fof(f357,plain,(
% 4.65/0.98    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0))) | ~v1_relat_1(sK2)) ) | ~spl6_3),
% 4.65/0.98    inference(resolution,[],[f119,f164])).
% 4.65/0.98  fof(f119,plain,(
% 4.65/0.98    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 4.65/0.98    inference(cnf_transformation,[],[f52])).
% 4.65/0.98  fof(f578,plain,(
% 4.65/0.98    spl6_42 | ~spl6_19 | ~spl6_41),
% 4.65/0.98    inference(avatar_split_clause,[],[f575,f536,f323,f540])).
% 4.65/0.98  fof(f323,plain,(
% 4.65/0.98    spl6_19 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 4.65/0.98  fof(f536,plain,(
% 4.65/0.98    spl6_41 <=> ! [X7] : k7_relset_1(sK0,sK1,sK2,X7) = k9_relat_1(sK2,X7)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 4.65/0.98  fof(f575,plain,(
% 4.65/0.98    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl6_19 | ~spl6_41)),
% 4.65/0.98    inference(backward_demodulation,[],[f325,f537])).
% 4.65/0.98  fof(f537,plain,(
% 4.65/0.98    ( ! [X7] : (k7_relset_1(sK0,sK1,sK2,X7) = k9_relat_1(sK2,X7)) ) | ~spl6_41),
% 4.65/0.98    inference(avatar_component_clause,[],[f536])).
% 4.65/0.98  fof(f325,plain,(
% 4.65/0.98    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl6_19),
% 4.65/0.98    inference(avatar_component_clause,[],[f323])).
% 4.65/0.98  fof(f557,plain,(
% 4.65/0.98    spl6_44 | ~spl6_9 | ~spl6_20),
% 4.65/0.98    inference(avatar_split_clause,[],[f548,f327,f194,f554])).
% 4.65/0.98  fof(f548,plain,(
% 4.65/0.98    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl6_9 | ~spl6_20)),
% 4.65/0.98    inference(backward_demodulation,[],[f329,f375])).
% 4.65/0.98  fof(f375,plain,(
% 4.65/0.98    ( ! [X7] : (k8_relset_1(sK0,sK1,sK2,X7) = k10_relat_1(sK2,X7)) ) | ~spl6_9),
% 4.65/0.98    inference(resolution,[],[f142,f196])).
% 4.65/0.98  fof(f329,plain,(
% 4.65/0.98    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl6_20),
% 4.65/0.98    inference(avatar_component_clause,[],[f327])).
% 4.65/0.98  fof(f552,plain,(
% 4.65/0.98    spl6_43 | ~spl6_9),
% 4.65/0.98    inference(avatar_split_clause,[],[f375,f194,f550])).
% 4.65/0.98  fof(f543,plain,(
% 4.65/0.98    ~spl6_42 | ~spl6_9 | spl6_19),
% 4.65/0.98    inference(avatar_split_clause,[],[f534,f323,f194,f540])).
% 4.65/0.98  fof(f534,plain,(
% 4.65/0.98    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl6_9 | spl6_19)),
% 4.65/0.98    inference(backward_demodulation,[],[f324,f361])).
% 4.65/0.98  fof(f361,plain,(
% 4.65/0.98    ( ! [X7] : (k7_relset_1(sK0,sK1,sK2,X7) = k9_relat_1(sK2,X7)) ) | ~spl6_9),
% 4.65/0.98    inference(resolution,[],[f141,f196])).
% 4.65/0.98  fof(f141,plain,(
% 4.65/0.98    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 4.65/0.98    inference(cnf_transformation,[],[f70])).
% 4.65/0.98  fof(f70,plain,(
% 4.65/0.98    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.65/0.98    inference(ennf_transformation,[],[f25])).
% 4.65/0.98  fof(f25,axiom,(
% 4.65/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 4.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 4.65/0.98  fof(f324,plain,(
% 4.65/0.98    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl6_19),
% 4.65/0.98    inference(avatar_component_clause,[],[f323])).
% 4.65/0.98  fof(f538,plain,(
% 4.65/0.98    spl6_41 | ~spl6_9),
% 4.65/0.98    inference(avatar_split_clause,[],[f361,f194,f536])).
% 4.65/0.98  fof(f527,plain,(
% 4.65/0.98    spl6_40 | ~spl6_3 | ~spl6_30),
% 4.65/0.98    inference(avatar_split_clause,[],[f523,f430,f162,f525])).
% 4.65/0.98  fof(f523,plain,(
% 4.65/0.98    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)) ) | (~spl6_3 | ~spl6_30)),
% 4.65/0.98    inference(subsumption_resolution,[],[f272,f431])).
% 4.65/0.98  fof(f272,plain,(
% 4.65/0.98    ( ! [X0] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) | ~v1_relat_1(sK2)) ) | ~spl6_3),
% 4.65/0.98    inference(resolution,[],[f116,f164])).
% 4.65/0.98  fof(f116,plain,(
% 4.65/0.98    ( ! [X0,X1] : (~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 4.65/0.98    inference(cnf_transformation,[],[f50])).
% 4.65/0.98  fof(f50,plain,(
% 4.65/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.65/0.98    inference(flattening,[],[f49])).
% 4.65/0.98  fof(f49,plain,(
% 4.65/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.65/0.98    inference(ennf_transformation,[],[f20])).
% 4.65/0.98  fof(f20,axiom,(
% 4.65/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 4.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 4.65/0.98  fof(f473,plain,(
% 4.65/0.98    spl6_36 | ~spl6_14 | ~spl6_30),
% 4.65/0.98    inference(avatar_split_clause,[],[f466,f430,f258,f470])).
% 4.65/0.98  fof(f258,plain,(
% 4.65/0.98    spl6_14 <=> v5_relat_1(sK2,sK1)),
% 4.65/0.98    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 4.65/0.98  fof(f466,plain,(
% 4.65/0.98    r1_tarski(k2_relat_1(sK2),sK1) | (~spl6_14 | ~spl6_30)),
% 4.65/0.98    inference(subsumption_resolution,[],[f264,f431])).
% 4.65/0.98  fof(f264,plain,(
% 4.65/0.98    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2) | ~spl6_14),
% 4.65/0.98    inference(resolution,[],[f260,f106])).
% 4.65/0.98  fof(f106,plain,(
% 4.65/0.98    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.65/0.98    inference(cnf_transformation,[],[f82])).
% 4.65/0.98  fof(f82,plain,(
% 4.65/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.65/0.98    inference(nnf_transformation,[],[f41])).
% 4.65/0.98  fof(f41,plain,(
% 4.65/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.65/0.98    inference(ennf_transformation,[],[f14])).
% 4.65/0.98  fof(f14,axiom,(
% 4.65/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 4.65/0.98  fof(f260,plain,(
% 4.65/0.98    v5_relat_1(sK2,sK1) | ~spl6_14),
% 4.65/0.98    inference(avatar_component_clause,[],[f258])).
% 4.65/0.98  fof(f444,plain,(
% 4.65/0.98    ~spl6_9 | spl6_30),
% 4.65/0.98    inference(avatar_contradiction_clause,[],[f443])).
% 4.65/0.98  fof(f443,plain,(
% 4.65/0.98    $false | (~spl6_9 | spl6_30)),
% 4.65/0.98    inference(unit_resulting_resolution,[],[f103,f196,f432,f101])).
% 4.65/0.98  fof(f101,plain,(
% 4.65/0.98    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 4.65/0.98    inference(cnf_transformation,[],[f37])).
% 4.65/0.98  fof(f37,plain,(
% 4.65/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.65/0.98    inference(ennf_transformation,[],[f12])).
% 4.65/0.98  fof(f12,axiom,(
% 4.65/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 4.65/0.98  fof(f432,plain,(
% 4.65/0.98    ~v1_relat_1(sK2) | spl6_30),
% 4.65/0.98    inference(avatar_component_clause,[],[f430])).
% 4.65/0.98  fof(f103,plain,(
% 4.65/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.65/0.98    inference(cnf_transformation,[],[f15])).
% 4.65/0.98  fof(f15,axiom,(
% 4.65/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 4.65/0.98  fof(f347,plain,(
% 4.65/0.98    ~spl6_19 | ~spl6_20),
% 4.65/0.98    inference(avatar_split_clause,[],[f341,f327,f323])).
% 4.65/0.98  fof(f341,plain,(
% 4.65/0.98    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl6_20),
% 4.65/0.98    inference(subsumption_resolution,[],[f97,f329])).
% 4.65/0.98  fof(f97,plain,(
% 4.65/0.98    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 4.65/0.98    inference(cnf_transformation,[],[f81])).
% 4.65/0.98  fof(f81,plain,(
% 4.65/0.98    (((((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 4.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f75,f80,f79,f78,f77,f76])).
% 4.65/0.98  fof(f76,plain,(
% 4.65/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 4.65/0.98    introduced(choice_axiom,[])).
% 4.65/0.98  fof(f77,plain,(
% 4.65/0.98    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,X1,X2,X4)) | r1_tarski(k7_relset_1(sK0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) & v1_funct_2(X2,sK0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) & ~v1_xboole_0(sK1))),
% 4.65/0.98    introduced(choice_axiom,[])).
% 4.65/0.98  fof(f78,plain,(
% 4.65/0.98    ? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,X2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X2,sK0,sK1) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 4.65/0.98    introduced(choice_axiom,[])).
% 4.65/0.98  fof(f79,plain,(
% 4.65/0.98    ? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & (r1_tarski(X3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (? [X4] : ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 4.65/0.98    introduced(choice_axiom,[])).
% 4.65/0.98  fof(f80,plain,(
% 4.65/0.98    ? [X4] : ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,X4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),X4)) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => ((~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & (r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 4.65/0.98    introduced(choice_axiom,[])).
% 4.65/0.98  fof(f75,plain,(
% 4.65/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 4.65/0.98    inference(flattening,[],[f74])).
% 4.65/0.98  fof(f74,plain,(
% 4.65/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | ~r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)) & (r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) | r1_tarski(k7_relset_1(X0,X1,X2,X3),X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 4.65/0.98    inference(nnf_transformation,[],[f36])).
% 4.65/0.99  fof(f36,plain,(
% 4.65/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 4.65/0.99    inference(flattening,[],[f35])).
% 4.65/0.99  fof(f35,plain,(
% 4.65/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 4.65/0.99    inference(ennf_transformation,[],[f34])).
% 4.65/0.99  fof(f34,negated_conjecture,(
% 4.65/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 4.65/0.99    inference(negated_conjecture,[],[f33])).
% 4.65/0.99  fof(f33,conjecture,(
% 4.65/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 4.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).
% 4.65/0.99  fof(f330,plain,(
% 4.65/0.99    spl6_19 | spl6_20),
% 4.65/0.99    inference(avatar_split_clause,[],[f96,f327,f323])).
% 4.65/0.99  fof(f96,plain,(
% 4.65/0.99    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 4.65/0.99    inference(cnf_transformation,[],[f81])).
% 4.65/0.99  fof(f261,plain,(
% 4.65/0.99    spl6_14 | ~spl6_9),
% 4.65/0.99    inference(avatar_split_clause,[],[f247,f194,f258])).
% 4.65/0.99  fof(f247,plain,(
% 4.65/0.99    v5_relat_1(sK2,sK1) | ~spl6_9),
% 4.65/0.99    inference(resolution,[],[f133,f196])).
% 4.65/0.99  fof(f133,plain,(
% 4.65/0.99    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 4.65/0.99    inference(cnf_transformation,[],[f60])).
% 4.65/0.99  fof(f60,plain,(
% 4.65/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.65/0.99    inference(ennf_transformation,[],[f22])).
% 4.65/0.99  fof(f22,axiom,(
% 4.65/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 4.65/0.99  fof(f208,plain,(
% 4.65/0.99    spl6_10 | ~spl6_6),
% 4.65/0.99    inference(avatar_split_clause,[],[f201,f177,f205])).
% 4.65/0.99  fof(f177,plain,(
% 4.65/0.99    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 4.65/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 4.65/0.99  fof(f201,plain,(
% 4.65/0.99    r1_tarski(sK3,sK0) | ~spl6_6),
% 4.65/0.99    inference(resolution,[],[f123,f179])).
% 4.65/0.99  fof(f179,plain,(
% 4.65/0.99    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_6),
% 4.65/0.99    inference(avatar_component_clause,[],[f177])).
% 4.65/0.99  fof(f123,plain,(
% 4.65/0.99    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 4.65/0.99    inference(cnf_transformation,[],[f86])).
% 4.65/0.99  fof(f86,plain,(
% 4.65/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.65/0.99    inference(nnf_transformation,[],[f10])).
% 4.65/0.99  fof(f10,axiom,(
% 4.65/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 4.65/0.99  fof(f197,plain,(
% 4.65/0.99    spl6_9),
% 4.65/0.99    inference(avatar_split_clause,[],[f93,f194])).
% 4.65/0.99  fof(f93,plain,(
% 4.65/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 4.65/0.99    inference(cnf_transformation,[],[f81])).
% 4.65/0.99  fof(f180,plain,(
% 4.65/0.99    spl6_6),
% 4.65/0.99    inference(avatar_split_clause,[],[f94,f177])).
% 4.65/0.99  fof(f94,plain,(
% 4.65/0.99    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 4.65/0.99    inference(cnf_transformation,[],[f81])).
% 4.65/0.99  fof(f175,plain,(
% 4.65/0.99    spl6_5),
% 4.65/0.99    inference(avatar_split_clause,[],[f92,f172])).
% 4.65/0.99  fof(f92,plain,(
% 4.65/0.99    v1_funct_2(sK2,sK0,sK1)),
% 4.65/0.99    inference(cnf_transformation,[],[f81])).
% 4.65/0.99  fof(f170,plain,(
% 4.65/0.99    spl6_4),
% 4.65/0.99    inference(avatar_split_clause,[],[f98,f167])).
% 4.65/0.99  fof(f167,plain,(
% 4.65/0.99    spl6_4 <=> v1_xboole_0(k1_xboole_0)),
% 4.65/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 4.65/0.99  fof(f98,plain,(
% 4.65/0.99    v1_xboole_0(k1_xboole_0)),
% 4.65/0.99    inference(cnf_transformation,[],[f1])).
% 4.65/0.99  fof(f1,axiom,(
% 4.65/0.99    v1_xboole_0(k1_xboole_0)),
% 4.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 4.65/0.99  fof(f165,plain,(
% 4.65/0.99    spl6_3),
% 4.65/0.99    inference(avatar_split_clause,[],[f91,f162])).
% 4.65/0.99  fof(f91,plain,(
% 4.65/0.99    v1_funct_1(sK2)),
% 4.65/0.99    inference(cnf_transformation,[],[f81])).
% 4.65/0.99  fof(f160,plain,(
% 4.65/0.99    ~spl6_2),
% 4.65/0.99    inference(avatar_split_clause,[],[f90,f157])).
% 4.65/0.99  fof(f157,plain,(
% 4.65/0.99    spl6_2 <=> v1_xboole_0(sK1)),
% 4.65/0.99    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 4.65/0.99  fof(f90,plain,(
% 4.65/0.99    ~v1_xboole_0(sK1)),
% 4.65/0.99    inference(cnf_transformation,[],[f81])).
% 4.65/0.99  % SZS output end Proof for theBenchmark
% 4.65/0.99  % (11565)------------------------------
% 4.65/0.99  % (11565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.65/0.99  % (11565)Termination reason: Refutation
% 4.65/0.99  
% 4.65/0.99  % (11565)Memory used [KB]: 10746
% 4.65/0.99  % (11565)Time elapsed: 0.561 s
% 4.65/0.99  % (11565)------------------------------
% 4.65/0.99  % (11565)------------------------------
% 4.65/0.99  % (11562)Success in time 0.621 s
%------------------------------------------------------------------------------
