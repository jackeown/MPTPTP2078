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
% DateTime   : Thu Dec  3 13:07:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  279 ( 508 expanded)
%              Number of leaves         :   62 ( 211 expanded)
%              Depth                    :   14
%              Number of atoms          :  966 (1776 expanded)
%              Number of equality atoms :  148 ( 316 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1600,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f137,f143,f148,f157,f176,f200,f215,f220,f225,f259,f288,f306,f343,f354,f381,f407,f518,f544,f565,f580,f586,f608,f673,f682,f701,f716,f749,f774,f800,f837,f939,f942,f954,f1311,f1339,f1513,f1547,f1599])).

fof(f1599,plain,
    ( ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | spl10_31
    | spl10_91
    | ~ spl10_135 ),
    inference(avatar_contradiction_clause,[],[f1598])).

fof(f1598,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | spl10_31
    | spl10_91
    | ~ spl10_135 ),
    inference(subsumption_resolution,[],[f1597,f60])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1597,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | spl10_31
    | spl10_91
    | ~ spl10_135 ),
    inference(forward_demodulation,[],[f1525,f1546])).

fof(f1546,plain,
    ( k1_xboole_0 = k2_relset_1(sK1,sK2,sK3)
    | ~ spl10_135 ),
    inference(avatar_component_clause,[],[f1544])).

fof(f1544,plain,
    ( spl10_135
  <=> k1_xboole_0 = k2_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_135])])).

fof(f1525,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | spl10_31
    | spl10_91 ),
    inference(resolution,[],[f832,f476])).

fof(f476,plain,
    ( ! [X1] :
        ( v1_funct_2(sK3,sK1,X1)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) )
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | spl10_31 ),
    inference(subsumption_resolution,[],[f193,f341])).

fof(f341,plain,
    ( k1_xboole_0 != sK2
    | spl10_31 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl10_31
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f193,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
        | k1_xboole_0 = sK2
        | v1_funct_2(sK3,sK1,X1) )
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f192,f116])).

fof(f116,plain,
    ( v1_funct_1(sK3)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl10_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f192,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
        | k1_xboole_0 = sK2
        | v1_funct_2(sK3,sK1,X1) )
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f184,f136])).

fof(f136,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl10_6
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f184,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK3,sK1,sK2)
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
        | k1_xboole_0 = sK2
        | v1_funct_2(sK3,sK1,X1) )
    | ~ spl10_8 ),
    inference(resolution,[],[f147,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f147,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl10_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f832,plain,
    ( ~ v1_funct_2(sK3,sK1,k1_xboole_0)
    | spl10_91 ),
    inference(avatar_component_clause,[],[f830])).

fof(f830,plain,
    ( spl10_91
  <=> v1_funct_2(sK3,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).

fof(f1547,plain,
    ( spl10_135
    | ~ spl10_86 ),
    inference(avatar_split_clause,[],[f808,f797,f1544])).

fof(f797,plain,
    ( spl10_86
  <=> v1_xboole_0(k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f808,plain,
    ( k1_xboole_0 = k2_relset_1(sK1,sK2,sK3)
    | ~ spl10_86 ),
    inference(resolution,[],[f799,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f799,plain,
    ( v1_xboole_0(k2_relset_1(sK1,sK2,sK3))
    | ~ spl10_86 ),
    inference(avatar_component_clause,[],[f797])).

fof(f1513,plain,
    ( spl10_10
    | ~ spl10_95
    | ~ spl10_97
    | ~ spl10_99
    | ~ spl10_128 ),
    inference(avatar_contradiction_clause,[],[f1512])).

fof(f1512,plain,
    ( $false
    | spl10_10
    | ~ spl10_95
    | ~ spl10_97
    | ~ spl10_99
    | ~ spl10_128 ),
    inference(subsumption_resolution,[],[f1507,f155])).

fof(f155,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl10_10
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f1507,plain,
    ( v1_xboole_0(sK1)
    | ~ spl10_95
    | ~ spl10_97
    | ~ spl10_99
    | ~ spl10_128 ),
    inference(resolution,[],[f1361,f71])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1361,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl10_95
    | ~ spl10_97
    | ~ spl10_99
    | ~ spl10_128 ),
    inference(forward_demodulation,[],[f1360,f850])).

fof(f850,plain,
    ( sK1 = k1_relat_1(k1_xboole_0)
    | ~ spl10_95 ),
    inference(avatar_component_clause,[],[f848])).

fof(f848,plain,
    ( spl10_95
  <=> sK1 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).

fof(f1360,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ spl10_97
    | ~ spl10_99
    | ~ spl10_128 ),
    inference(subsumption_resolution,[],[f1359,f953])).

fof(f953,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl10_99 ),
    inference(avatar_component_clause,[],[f951])).

fof(f951,plain,
    ( spl10_99
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f1359,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl10_97
    | ~ spl10_128 ),
    inference(subsumption_resolution,[],[f1354,f938])).

fof(f938,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl10_97 ),
    inference(avatar_component_clause,[],[f936])).

fof(f936,plain,
    ( spl10_97
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).

fof(f1354,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl10_128 ),
    inference(resolution,[],[f1345,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f1345,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl10_128 ),
    inference(subsumption_resolution,[],[f1342,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1342,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl10_128 ),
    inference(resolution,[],[f1338,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f1338,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_128 ),
    inference(avatar_component_clause,[],[f1336])).

fof(f1336,plain,
    ( spl10_128
  <=> m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_128])])).

fof(f1339,plain,
    ( spl10_128
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f1318,f1308,f1336])).

fof(f1308,plain,
    ( spl10_124
  <=> r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).

fof(f1318,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_124 ),
    inference(resolution,[],[f1310,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1310,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl10_124 ),
    inference(avatar_component_clause,[],[f1308])).

fof(f1311,plain,
    ( spl10_124
    | ~ spl10_64
    | ~ spl10_80
    | ~ spl10_92 ),
    inference(avatar_split_clause,[],[f925,f834,f698,f577,f1308])).

fof(f577,plain,
    ( spl10_64
  <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f698,plain,
    ( spl10_80
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f834,plain,
    ( spl10_92
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f925,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl10_64
    | ~ spl10_80
    | ~ spl10_92 ),
    inference(forward_demodulation,[],[f894,f700])).

fof(f700,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl10_80 ),
    inference(avatar_component_clause,[],[f698])).

fof(f894,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK4))
    | ~ spl10_64
    | ~ spl10_92 ),
    inference(superposition,[],[f579,f836])).

fof(f836,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_92 ),
    inference(avatar_component_clause,[],[f834])).

fof(f579,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f577])).

fof(f954,plain,
    ( spl10_99
    | ~ spl10_14
    | ~ spl10_92 ),
    inference(avatar_split_clause,[],[f860,f834,f222,f951])).

fof(f222,plain,
    ( spl10_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f860,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl10_14
    | ~ spl10_92 ),
    inference(superposition,[],[f224,f836])).

fof(f224,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f222])).

fof(f942,plain,
    ( k1_xboole_0 != sK3
    | sK1 != k1_relset_1(sK1,sK2,sK3)
    | k1_relset_1(sK1,sK2,sK3) != k1_relat_1(sK3)
    | sK1 = k1_relat_1(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f939,plain,
    ( spl10_97
    | ~ spl10_2
    | ~ spl10_92 ),
    inference(avatar_split_clause,[],[f855,f834,f114,f936])).

fof(f855,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl10_2
    | ~ spl10_92 ),
    inference(superposition,[],[f116,f836])).

fof(f837,plain,
    ( ~ spl10_91
    | spl10_92
    | spl10_5
    | ~ spl10_83 ),
    inference(avatar_split_clause,[],[f793,f767,f129,f834,f830])).

fof(f129,plain,
    ( spl10_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f767,plain,
    ( spl10_83
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f793,plain,
    ( k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK1,k1_xboole_0)
    | spl10_5
    | ~ spl10_83 ),
    inference(subsumption_resolution,[],[f780,f131])).

fof(f131,plain,
    ( k1_xboole_0 != sK1
    | spl10_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f780,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK1,k1_xboole_0)
    | ~ spl10_83 ),
    inference(resolution,[],[f768,f103])).

fof(f103,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f768,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl10_83 ),
    inference(avatar_component_clause,[],[f767])).

fof(f800,plain,
    ( spl10_86
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f765,f516,f797])).

fof(f516,plain,
    ( spl10_56
  <=> ! [X0] : ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f765,plain,
    ( v1_xboole_0(k2_relset_1(sK1,sK2,sK3))
    | ~ spl10_56 ),
    inference(resolution,[],[f517,f71])).

fof(f517,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f516])).

fof(f774,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f749,plain,
    ( spl10_55
    | ~ spl10_80 ),
    inference(avatar_contradiction_clause,[],[f748])).

fof(f748,plain,
    ( $false
    | spl10_55
    | ~ spl10_80 ),
    inference(subsumption_resolution,[],[f729,f59])).

fof(f729,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_55
    | ~ spl10_80 ),
    inference(superposition,[],[f514,f700])).

fof(f514,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK4))
    | spl10_55 ),
    inference(avatar_component_clause,[],[f512])).

fof(f512,plain,
    ( spl10_55
  <=> v1_xboole_0(k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f716,plain,
    ( ~ spl10_2
    | ~ spl10_9
    | ~ spl10_61
    | spl10_76
    | ~ spl10_79
    | spl10_80 ),
    inference(avatar_contradiction_clause,[],[f715])).

fof(f715,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_9
    | ~ spl10_61
    | spl10_76
    | ~ spl10_79
    | spl10_80 ),
    inference(subsumption_resolution,[],[f713,f152])).

fof(f152,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl10_9
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f713,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ spl10_2
    | ~ spl10_61
    | spl10_76
    | ~ spl10_79
    | spl10_80 ),
    inference(resolution,[],[f711,f681])).

fof(f681,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl10_76 ),
    inference(avatar_component_clause,[],[f679])).

fof(f679,plain,
    ( spl10_76
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f711,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_2
    | ~ spl10_61
    | ~ spl10_79
    | spl10_80 ),
    inference(subsumption_resolution,[],[f710,f699])).

fof(f699,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | spl10_80 ),
    inference(avatar_component_clause,[],[f698])).

fof(f710,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k1_xboole_0 = k1_relat_1(sK4)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) )
    | ~ spl10_2
    | ~ spl10_61
    | ~ spl10_79 ),
    inference(subsumption_resolution,[],[f558,f696])).

fof(f696,plain,
    ( v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | ~ spl10_79 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl10_79
  <=> v1_funct_2(sK3,sK1,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f558,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4))
        | ~ r2_hidden(X0,sK1)
        | k1_xboole_0 = k1_relat_1(sK4)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) )
    | ~ spl10_2
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f551,f116])).

fof(f551,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4))
        | ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,sK1)
        | k1_xboole_0 = k1_relat_1(sK4)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) )
    | ~ spl10_61 ),
    inference(resolution,[],[f542,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f542,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl10_61
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f701,plain,
    ( spl10_79
    | spl10_80
    | ~ spl10_61
    | ~ spl10_75 ),
    inference(avatar_split_clause,[],[f692,f670,f540,f698,f694])).

fof(f670,plain,
    ( spl10_75
  <=> sK1 = k1_relset_1(sK1,k1_relat_1(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f692,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | ~ spl10_61
    | ~ spl10_75 ),
    inference(subsumption_resolution,[],[f549,f672])).

fof(f672,plain,
    ( sK1 = k1_relset_1(sK1,k1_relat_1(sK4),sK3)
    | ~ spl10_75 ),
    inference(avatar_component_clause,[],[f670])).

fof(f549,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | sK1 != k1_relset_1(sK1,k1_relat_1(sK4),sK3)
    | v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | ~ spl10_61 ),
    inference(resolution,[],[f542,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f682,plain,
    ( ~ spl10_76
    | ~ spl10_1
    | ~ spl10_12
    | ~ spl10_16
    | spl10_68 ),
    inference(avatar_split_clause,[],[f611,f605,f256,f212,f109,f679])).

fof(f109,plain,
    ( spl10_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f212,plain,
    ( spl10_12
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f256,plain,
    ( spl10_16
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f605,plain,
    ( spl10_68
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f611,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ spl10_1
    | ~ spl10_12
    | ~ spl10_16
    | spl10_68 ),
    inference(subsumption_resolution,[],[f610,f258])).

fof(f258,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f256])).

fof(f610,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v5_relat_1(sK4,sK0)
    | ~ spl10_1
    | ~ spl10_12
    | spl10_68 ),
    inference(trivial_inequality_removal,[],[f609])).

fof(f609,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v5_relat_1(sK4,sK0)
    | ~ spl10_1
    | ~ spl10_12
    | spl10_68 ),
    inference(superposition,[],[f607,f235])).

fof(f235,plain,
    ( ! [X6,X7] :
        ( k7_partfun1(X6,sK4,X7) = k1_funct_1(sK4,X7)
        | ~ r2_hidden(X7,k1_relat_1(sK4))
        | ~ v5_relat_1(sK4,X6) )
    | ~ spl10_1
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f230,f111])).

fof(f111,plain,
    ( v1_funct_1(sK4)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f230,plain,
    ( ! [X6,X7] :
        ( ~ v5_relat_1(sK4,X6)
        | ~ v1_funct_1(sK4)
        | ~ r2_hidden(X7,k1_relat_1(sK4))
        | k7_partfun1(X6,sK4,X7) = k1_funct_1(sK4,X7) )
    | ~ spl10_12 ),
    inference(resolution,[],[f214,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f214,plain,
    ( v1_relat_1(sK4)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f212])).

fof(f607,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl10_68 ),
    inference(avatar_component_clause,[],[f605])).

fof(f673,plain,
    ( spl10_75
    | ~ spl10_32
    | ~ spl10_61 ),
    inference(avatar_split_clause,[],[f557,f540,f345,f670])).

fof(f345,plain,
    ( spl10_32
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f557,plain,
    ( sK1 = k1_relset_1(sK1,k1_relat_1(sK4),sK3)
    | ~ spl10_32
    | ~ spl10_61 ),
    inference(forward_demodulation,[],[f546,f347])).

fof(f347,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f345])).

fof(f546,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK1,k1_relat_1(sK4),sK3)
    | ~ spl10_61 ),
    inference(resolution,[],[f542,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f608,plain,
    ( ~ spl10_68
    | spl10_13
    | ~ spl10_65 ),
    inference(avatar_split_clause,[],[f589,f583,f217,f605])).

fof(f217,plain,
    ( spl10_13
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f583,plain,
    ( spl10_65
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f589,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl10_13
    | ~ spl10_65 ),
    inference(superposition,[],[f219,f585])).

fof(f585,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl10_65 ),
    inference(avatar_component_clause,[],[f583])).

fof(f219,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl10_13 ),
    inference(avatar_component_clause,[],[f217])).

fof(f586,plain,
    ( spl10_65
    | ~ spl10_1
    | ~ spl10_2
    | spl10_3
    | ~ spl10_4
    | spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f498,f197,f145,f140,f134,f129,f124,f119,f114,f109,f583])).

fof(f119,plain,
    ( spl10_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f124,plain,
    ( spl10_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f140,plain,
    ( spl10_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f197,plain,
    ( spl10_11
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f498,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl10_1
    | ~ spl10_2
    | spl10_3
    | ~ spl10_4
    | spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(resolution,[],[f210,f126])).

fof(f126,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl10_1
    | ~ spl10_2
    | spl10_3
    | spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f209,f131])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl10_1
    | ~ spl10_2
    | spl10_3
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f208,f121])).

fof(f121,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f207,f142])).

fof(f142,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f140])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f206,f111])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f205,f147])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f204,f136])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl10_2
    | ~ spl10_11 ),
    inference(subsumption_resolution,[],[f201,f116])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl10_11 ),
    inference(resolution,[],[f199,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | v1_xboole_0(X2)
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f199,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f197])).

fof(f580,plain,
    ( spl10_64
    | ~ spl10_14
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f567,f562,f222,f577])).

fof(f562,plain,
    ( spl10_62
  <=> v5_relat_1(sK3,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f567,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl10_14
    | ~ spl10_62 ),
    inference(resolution,[],[f564,f241])).

fof(f241,plain,
    ( ! [X5] :
        ( ~ v5_relat_1(sK3,X5)
        | r1_tarski(k2_relat_1(sK3),X5) )
    | ~ spl10_14 ),
    inference(resolution,[],[f224,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f564,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f562])).

fof(f565,plain,
    ( spl10_62
    | ~ spl10_61 ),
    inference(avatar_split_clause,[],[f548,f540,f562])).

fof(f548,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ spl10_61 ),
    inference(resolution,[],[f542,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f544,plain,
    ( spl10_61
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_11
    | ~ spl10_21
    | spl10_31 ),
    inference(avatar_split_clause,[],[f489,f340,f285,f197,f145,f134,f114,f540])).

fof(f285,plain,
    ( spl10_21
  <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f489,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_11
    | ~ spl10_21
    | spl10_31 ),
    inference(forward_demodulation,[],[f488,f287])).

fof(f287,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f285])).

fof(f488,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4))))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_11
    | spl10_31 ),
    inference(resolution,[],[f482,f199])).

fof(f482,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) )
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | spl10_31 ),
    inference(subsumption_resolution,[],[f195,f341])).

fof(f195,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
        | k1_xboole_0 = sK2
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) )
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f194,f116])).

fof(f194,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK3)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
        | k1_xboole_0 = sK2
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) )
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f185,f136])).

fof(f185,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(sK3,sK1,sK2)
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X2)
        | k1_xboole_0 = sK2
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) )
    | ~ spl10_8 ),
    inference(resolution,[],[f147,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f518,plain,
    ( ~ spl10_55
    | spl10_56
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f408,f404,f516,f512])).

fof(f404,plain,
    ( spl10_37
  <=> m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(k1_relat_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f408,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))
        | ~ v1_xboole_0(k1_relat_1(sK4)) )
    | ~ spl10_37 ),
    inference(resolution,[],[f406,f92])).

fof(f406,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(k1_relat_1(sK4)))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f404])).

fof(f407,plain,
    ( spl10_37
    | ~ spl10_11
    | ~ spl10_21 ),
    inference(avatar_split_clause,[],[f397,f285,f197,f404])).

fof(f397,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(k1_relat_1(sK4)))
    | ~ spl10_11
    | ~ spl10_21 ),
    inference(forward_demodulation,[],[f203,f287])).

fof(f203,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(k1_relset_1(sK2,sK0,sK4)))
    | ~ spl10_11 ),
    inference(resolution,[],[f199,f78])).

fof(f381,plain,
    ( spl10_3
    | ~ spl10_31 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | spl10_3
    | ~ spl10_31 ),
    inference(subsumption_resolution,[],[f363,f59])).

fof(f363,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_3
    | ~ spl10_31 ),
    inference(superposition,[],[f121,f342])).

fof(f342,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f340])).

fof(f354,plain,
    ( spl10_32
    | ~ spl10_25
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f348,f336,f303,f345])).

fof(f303,plain,
    ( spl10_25
  <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f336,plain,
    ( spl10_30
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f348,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl10_25
    | ~ spl10_30 ),
    inference(superposition,[],[f338,f305])).

fof(f305,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f303])).

fof(f338,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f336])).

fof(f343,plain,
    ( spl10_30
    | spl10_31
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f189,f145,f134,f340,f336])).

fof(f189,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f182,f136])).

fof(f182,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ spl10_8 ),
    inference(resolution,[],[f147,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f306,plain,
    ( spl10_25
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f178,f145,f303])).

fof(f178,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f147,f83])).

fof(f288,plain,
    ( spl10_21
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f159,f140,f285])).

fof(f159,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl10_7 ),
    inference(resolution,[],[f142,f83])).

fof(f259,plain,
    ( spl10_16
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f161,f140,f256])).

fof(f161,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl10_7 ),
    inference(resolution,[],[f142,f85])).

fof(f225,plain,
    ( spl10_14
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f177,f145,f222])).

fof(f177,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_8 ),
    inference(resolution,[],[f147,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f220,plain,(
    ~ spl10_13 ),
    inference(avatar_split_clause,[],[f52,f217])).

fof(f52,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f215,plain,
    ( spl10_12
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f158,f140,f212])).

fof(f158,plain,
    ( v1_relat_1(sK4)
    | ~ spl10_7 ),
    inference(resolution,[],[f142,f82])).

fof(f200,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f50,f197])).

fof(f50,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f176,plain,
    ( spl10_5
    | ~ spl10_10 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl10_5
    | ~ spl10_10 ),
    inference(subsumption_resolution,[],[f174,f131])).

fof(f174,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_10 ),
    inference(resolution,[],[f156,f62])).

fof(f156,plain,
    ( v1_xboole_0(sK1)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f157,plain,
    ( spl10_9
    | spl10_10
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f138,f124,f154,f150])).

fof(f138,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5,sK1)
    | ~ spl10_4 ),
    inference(resolution,[],[f126,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f148,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f57,f145])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f143,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f54,f140])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f137,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f56,f134])).

fof(f56,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f132,plain,(
    ~ spl10_5 ),
    inference(avatar_split_clause,[],[f51,f129])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f127,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f49,f124])).

fof(f49,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f122,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f58,f119])).

fof(f58,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f117,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f55,f114])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f112,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f53,f109])).

fof(f53,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:30:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.44  % (32560)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (32548)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (32549)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (32554)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (32556)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (32555)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (32551)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (32552)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (32562)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (32568)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (32568)Refutation not found, incomplete strategy% (32568)------------------------------
% 0.22/0.50  % (32568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (32568)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (32568)Memory used [KB]: 10618
% 0.22/0.50  % (32568)Time elapsed: 0.084 s
% 0.22/0.50  % (32568)------------------------------
% 0.22/0.50  % (32568)------------------------------
% 0.22/0.50  % (32557)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (32566)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (32567)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (32564)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (32559)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (32550)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (32553)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (32548)Refutation not found, incomplete strategy% (32548)------------------------------
% 0.22/0.51  % (32548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32548)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (32548)Memory used [KB]: 6652
% 0.22/0.51  % (32548)Time elapsed: 0.083 s
% 0.22/0.51  % (32548)------------------------------
% 0.22/0.51  % (32548)------------------------------
% 0.22/0.51  % (32561)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (32565)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (32558)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (32549)Refutation not found, incomplete strategy% (32549)------------------------------
% 0.22/0.52  % (32549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32549)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32549)Memory used [KB]: 10746
% 0.22/0.52  % (32549)Time elapsed: 0.102 s
% 0.22/0.52  % (32549)------------------------------
% 0.22/0.52  % (32549)------------------------------
% 0.22/0.53  % (32563)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.53  % (32559)Refutation not found, incomplete strategy% (32559)------------------------------
% 0.22/0.53  % (32559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32559)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32559)Memory used [KB]: 10874
% 0.22/0.53  % (32559)Time elapsed: 0.096 s
% 0.22/0.53  % (32559)------------------------------
% 0.22/0.53  % (32559)------------------------------
% 0.22/0.55  % (32551)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f1600,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f137,f143,f148,f157,f176,f200,f215,f220,f225,f259,f288,f306,f343,f354,f381,f407,f518,f544,f565,f580,f586,f608,f673,f682,f701,f716,f749,f774,f800,f837,f939,f942,f954,f1311,f1339,f1513,f1547,f1599])).
% 0.22/0.55  fof(f1599,plain,(
% 0.22/0.55    ~spl10_2 | ~spl10_6 | ~spl10_8 | spl10_31 | spl10_91 | ~spl10_135),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f1598])).
% 0.22/0.55  fof(f1598,plain,(
% 0.22/0.55    $false | (~spl10_2 | ~spl10_6 | ~spl10_8 | spl10_31 | spl10_91 | ~spl10_135)),
% 0.22/0.55    inference(subsumption_resolution,[],[f1597,f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.55  fof(f1597,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl10_2 | ~spl10_6 | ~spl10_8 | spl10_31 | spl10_91 | ~spl10_135)),
% 0.22/0.55    inference(forward_demodulation,[],[f1525,f1546])).
% 0.22/0.55  fof(f1546,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relset_1(sK1,sK2,sK3) | ~spl10_135),
% 0.22/0.55    inference(avatar_component_clause,[],[f1544])).
% 0.22/0.55  fof(f1544,plain,(
% 0.22/0.55    spl10_135 <=> k1_xboole_0 = k2_relset_1(sK1,sK2,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_135])])).
% 0.22/0.55  fof(f1525,plain,(
% 0.22/0.55    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | (~spl10_2 | ~spl10_6 | ~spl10_8 | spl10_31 | spl10_91)),
% 0.22/0.55    inference(resolution,[],[f832,f476])).
% 0.22/0.55  fof(f476,plain,(
% 0.22/0.55    ( ! [X1] : (v1_funct_2(sK3,sK1,X1) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)) ) | (~spl10_2 | ~spl10_6 | ~spl10_8 | spl10_31)),
% 0.22/0.55    inference(subsumption_resolution,[],[f193,f341])).
% 0.22/0.55  fof(f341,plain,(
% 0.22/0.55    k1_xboole_0 != sK2 | spl10_31),
% 0.22/0.55    inference(avatar_component_clause,[],[f340])).
% 0.22/0.55  fof(f340,plain,(
% 0.22/0.55    spl10_31 <=> k1_xboole_0 = sK2),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 0.22/0.55  fof(f193,plain,(
% 0.22/0.55    ( ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,X1)) ) | (~spl10_2 | ~spl10_6 | ~spl10_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f192,f116])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    v1_funct_1(sK3) | ~spl10_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f114])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    spl10_2 <=> v1_funct_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.55  fof(f192,plain,(
% 0.22/0.55    ( ! [X1] : (~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,X1)) ) | (~spl10_6 | ~spl10_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f184,f136])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK1,sK2) | ~spl10_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f134])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    spl10_6 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.55  fof(f184,plain,(
% 0.22/0.55    ( ! [X1] : (~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,X1)) ) | ~spl10_8),
% 0.22/0.55    inference(resolution,[],[f147,f96])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | v1_funct_2(X3,X0,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.55    inference(flattening,[],[f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl10_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f145])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    spl10_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.55  fof(f832,plain,(
% 0.22/0.55    ~v1_funct_2(sK3,sK1,k1_xboole_0) | spl10_91),
% 0.22/0.55    inference(avatar_component_clause,[],[f830])).
% 0.22/0.55  fof(f830,plain,(
% 0.22/0.55    spl10_91 <=> v1_funct_2(sK3,sK1,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).
% 0.22/0.55  fof(f1547,plain,(
% 0.22/0.55    spl10_135 | ~spl10_86),
% 0.22/0.55    inference(avatar_split_clause,[],[f808,f797,f1544])).
% 0.22/0.55  fof(f797,plain,(
% 0.22/0.55    spl10_86 <=> v1_xboole_0(k2_relset_1(sK1,sK2,sK3))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).
% 0.22/0.55  fof(f808,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relset_1(sK1,sK2,sK3) | ~spl10_86),
% 0.22/0.55    inference(resolution,[],[f799,f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.55  fof(f799,plain,(
% 0.22/0.55    v1_xboole_0(k2_relset_1(sK1,sK2,sK3)) | ~spl10_86),
% 0.22/0.55    inference(avatar_component_clause,[],[f797])).
% 0.22/0.55  fof(f1513,plain,(
% 0.22/0.55    spl10_10 | ~spl10_95 | ~spl10_97 | ~spl10_99 | ~spl10_128),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f1512])).
% 0.22/0.55  fof(f1512,plain,(
% 0.22/0.55    $false | (spl10_10 | ~spl10_95 | ~spl10_97 | ~spl10_99 | ~spl10_128)),
% 0.22/0.55    inference(subsumption_resolution,[],[f1507,f155])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    ~v1_xboole_0(sK1) | spl10_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f154])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    spl10_10 <=> v1_xboole_0(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.22/0.55  fof(f1507,plain,(
% 0.22/0.55    v1_xboole_0(sK1) | (~spl10_95 | ~spl10_97 | ~spl10_99 | ~spl10_128)),
% 0.22/0.55    inference(resolution,[],[f1361,f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK9(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.55  fof(f1361,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (~spl10_95 | ~spl10_97 | ~spl10_99 | ~spl10_128)),
% 0.22/0.55    inference(forward_demodulation,[],[f1360,f850])).
% 0.22/0.55  fof(f850,plain,(
% 0.22/0.55    sK1 = k1_relat_1(k1_xboole_0) | ~spl10_95),
% 0.22/0.55    inference(avatar_component_clause,[],[f848])).
% 0.22/0.55  fof(f848,plain,(
% 0.22/0.55    spl10_95 <=> sK1 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).
% 0.22/0.55  fof(f1360,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) ) | (~spl10_97 | ~spl10_99 | ~spl10_128)),
% 0.22/0.55    inference(subsumption_resolution,[],[f1359,f953])).
% 0.22/0.55  fof(f953,plain,(
% 0.22/0.55    v1_relat_1(k1_xboole_0) | ~spl10_99),
% 0.22/0.55    inference(avatar_component_clause,[],[f951])).
% 0.22/0.55  fof(f951,plain,(
% 0.22/0.55    spl10_99 <=> v1_relat_1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).
% 0.22/0.55  fof(f1359,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | (~spl10_97 | ~spl10_128)),
% 0.22/0.55    inference(subsumption_resolution,[],[f1354,f938])).
% 0.22/0.55  fof(f938,plain,(
% 0.22/0.55    v1_funct_1(k1_xboole_0) | ~spl10_97),
% 0.22/0.55    inference(avatar_component_clause,[],[f936])).
% 0.22/0.55  fof(f936,plain,(
% 0.22/0.55    spl10_97 <=> v1_funct_1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).
% 0.22/0.55  fof(f1354,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_1(k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl10_128),
% 0.22/0.55    inference(resolution,[],[f1345,f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.22/0.55  fof(f1345,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) ) | ~spl10_128),
% 0.22/0.55    inference(subsumption_resolution,[],[f1342,f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.55  fof(f1342,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)) ) | ~spl10_128),
% 0.22/0.55    inference(resolution,[],[f1338,f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.55  fof(f1338,plain,(
% 0.22/0.55    m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl10_128),
% 0.22/0.55    inference(avatar_component_clause,[],[f1336])).
% 0.22/0.55  fof(f1336,plain,(
% 0.22/0.55    spl10_128 <=> m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_128])])).
% 0.22/0.55  fof(f1339,plain,(
% 0.22/0.55    spl10_128 | ~spl10_124),
% 0.22/0.55    inference(avatar_split_clause,[],[f1318,f1308,f1336])).
% 0.22/0.55  fof(f1308,plain,(
% 0.22/0.55    spl10_124 <=> r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).
% 0.22/0.55  fof(f1318,plain,(
% 0.22/0.55    m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl10_124),
% 0.22/0.55    inference(resolution,[],[f1310,f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.55  fof(f1310,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | ~spl10_124),
% 0.22/0.55    inference(avatar_component_clause,[],[f1308])).
% 0.22/0.55  fof(f1311,plain,(
% 0.22/0.55    spl10_124 | ~spl10_64 | ~spl10_80 | ~spl10_92),
% 0.22/0.55    inference(avatar_split_clause,[],[f925,f834,f698,f577,f1308])).
% 0.22/0.55  fof(f577,plain,(
% 0.22/0.55    spl10_64 <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).
% 0.22/0.55  fof(f698,plain,(
% 0.22/0.55    spl10_80 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).
% 0.22/0.55  fof(f834,plain,(
% 0.22/0.55    spl10_92 <=> k1_xboole_0 = sK3),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).
% 0.22/0.55  fof(f925,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | (~spl10_64 | ~spl10_80 | ~spl10_92)),
% 0.22/0.55    inference(forward_demodulation,[],[f894,f700])).
% 0.22/0.55  fof(f700,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(sK4) | ~spl10_80),
% 0.22/0.55    inference(avatar_component_clause,[],[f698])).
% 0.22/0.55  fof(f894,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(k1_xboole_0),k1_relat_1(sK4)) | (~spl10_64 | ~spl10_92)),
% 0.22/0.55    inference(superposition,[],[f579,f836])).
% 0.22/0.55  fof(f836,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | ~spl10_92),
% 0.22/0.55    inference(avatar_component_clause,[],[f834])).
% 0.22/0.55  fof(f579,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~spl10_64),
% 0.22/0.55    inference(avatar_component_clause,[],[f577])).
% 0.22/0.55  fof(f954,plain,(
% 0.22/0.55    spl10_99 | ~spl10_14 | ~spl10_92),
% 0.22/0.55    inference(avatar_split_clause,[],[f860,f834,f222,f951])).
% 0.22/0.55  fof(f222,plain,(
% 0.22/0.55    spl10_14 <=> v1_relat_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.22/0.55  fof(f860,plain,(
% 0.22/0.55    v1_relat_1(k1_xboole_0) | (~spl10_14 | ~spl10_92)),
% 0.22/0.55    inference(superposition,[],[f224,f836])).
% 0.22/0.55  fof(f224,plain,(
% 0.22/0.55    v1_relat_1(sK3) | ~spl10_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f222])).
% 0.22/0.55  fof(f942,plain,(
% 0.22/0.55    k1_xboole_0 != sK3 | sK1 != k1_relset_1(sK1,sK2,sK3) | k1_relset_1(sK1,sK2,sK3) != k1_relat_1(sK3) | sK1 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.55  fof(f939,plain,(
% 0.22/0.55    spl10_97 | ~spl10_2 | ~spl10_92),
% 0.22/0.55    inference(avatar_split_clause,[],[f855,f834,f114,f936])).
% 0.22/0.55  fof(f855,plain,(
% 0.22/0.55    v1_funct_1(k1_xboole_0) | (~spl10_2 | ~spl10_92)),
% 0.22/0.55    inference(superposition,[],[f116,f836])).
% 0.22/0.55  fof(f837,plain,(
% 0.22/0.55    ~spl10_91 | spl10_92 | spl10_5 | ~spl10_83),
% 0.22/0.55    inference(avatar_split_clause,[],[f793,f767,f129,f834,f830])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    spl10_5 <=> k1_xboole_0 = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.55  fof(f767,plain,(
% 0.22/0.55    spl10_83 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).
% 0.22/0.55  fof(f793,plain,(
% 0.22/0.55    k1_xboole_0 = sK3 | ~v1_funct_2(sK3,sK1,k1_xboole_0) | (spl10_5 | ~spl10_83)),
% 0.22/0.55    inference(subsumption_resolution,[],[f780,f131])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    k1_xboole_0 != sK1 | spl10_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f129])).
% 0.22/0.55  fof(f780,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK3 | ~v1_funct_2(sK3,sK1,k1_xboole_0) | ~spl10_83),
% 0.22/0.55    inference(resolution,[],[f768,f103])).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f87])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.55  fof(f768,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~spl10_83),
% 0.22/0.55    inference(avatar_component_clause,[],[f767])).
% 0.22/0.55  fof(f800,plain,(
% 0.22/0.55    spl10_86 | ~spl10_56),
% 0.22/0.55    inference(avatar_split_clause,[],[f765,f516,f797])).
% 0.22/0.55  fof(f516,plain,(
% 0.22/0.55    spl10_56 <=> ! [X0] : ~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).
% 0.22/0.55  fof(f765,plain,(
% 0.22/0.55    v1_xboole_0(k2_relset_1(sK1,sK2,sK3)) | ~spl10_56),
% 0.22/0.55    inference(resolution,[],[f517,f71])).
% 0.22/0.55  fof(f517,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))) ) | ~spl10_56),
% 0.22/0.55    inference(avatar_component_clause,[],[f516])).
% 0.22/0.55  fof(f774,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relat_1(sK4) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))),
% 0.22/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.55  fof(f749,plain,(
% 0.22/0.55    spl10_55 | ~spl10_80),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f748])).
% 0.22/0.55  fof(f748,plain,(
% 0.22/0.55    $false | (spl10_55 | ~spl10_80)),
% 0.22/0.55    inference(subsumption_resolution,[],[f729,f59])).
% 0.22/0.55  fof(f729,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_xboole_0) | (spl10_55 | ~spl10_80)),
% 0.22/0.55    inference(superposition,[],[f514,f700])).
% 0.22/0.55  fof(f514,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_relat_1(sK4)) | spl10_55),
% 0.22/0.55    inference(avatar_component_clause,[],[f512])).
% 0.22/0.55  fof(f512,plain,(
% 0.22/0.55    spl10_55 <=> v1_xboole_0(k1_relat_1(sK4))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).
% 0.22/0.55  fof(f716,plain,(
% 0.22/0.55    ~spl10_2 | ~spl10_9 | ~spl10_61 | spl10_76 | ~spl10_79 | spl10_80),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f715])).
% 0.22/0.55  fof(f715,plain,(
% 0.22/0.55    $false | (~spl10_2 | ~spl10_9 | ~spl10_61 | spl10_76 | ~spl10_79 | spl10_80)),
% 0.22/0.55    inference(subsumption_resolution,[],[f713,f152])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    r2_hidden(sK5,sK1) | ~spl10_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f150])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    spl10_9 <=> r2_hidden(sK5,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.22/0.55  fof(f713,plain,(
% 0.22/0.55    ~r2_hidden(sK5,sK1) | (~spl10_2 | ~spl10_61 | spl10_76 | ~spl10_79 | spl10_80)),
% 0.22/0.55    inference(resolution,[],[f711,f681])).
% 0.22/0.55  fof(f681,plain,(
% 0.22/0.55    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl10_76),
% 0.22/0.55    inference(avatar_component_clause,[],[f679])).
% 0.22/0.55  fof(f679,plain,(
% 0.22/0.55    spl10_76 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).
% 0.22/0.55  fof(f711,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) | ~r2_hidden(X0,sK1)) ) | (~spl10_2 | ~spl10_61 | ~spl10_79 | spl10_80)),
% 0.22/0.55    inference(subsumption_resolution,[],[f710,f699])).
% 0.22/0.55  fof(f699,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relat_1(sK4) | spl10_80),
% 0.22/0.55    inference(avatar_component_clause,[],[f698])).
% 0.22/0.55  fof(f710,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = k1_relat_1(sK4) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) ) | (~spl10_2 | ~spl10_61 | ~spl10_79)),
% 0.22/0.55    inference(subsumption_resolution,[],[f558,f696])).
% 0.22/0.55  fof(f696,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~spl10_79),
% 0.22/0.55    inference(avatar_component_clause,[],[f694])).
% 0.22/0.55  fof(f694,plain,(
% 0.22/0.55    spl10_79 <=> v1_funct_2(sK3,sK1,k1_relat_1(sK4))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).
% 0.22/0.55  fof(f558,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~r2_hidden(X0,sK1) | k1_xboole_0 = k1_relat_1(sK4) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) ) | (~spl10_2 | ~spl10_61)),
% 0.22/0.55    inference(subsumption_resolution,[],[f551,f116])).
% 0.22/0.55  fof(f551,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~r2_hidden(X0,sK1) | k1_xboole_0 = k1_relat_1(sK4) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) ) | ~spl10_61),
% 0.22/0.55    inference(resolution,[],[f542,f93])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.55    inference(flattening,[],[f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.55  fof(f542,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | ~spl10_61),
% 0.22/0.55    inference(avatar_component_clause,[],[f540])).
% 0.22/0.55  fof(f540,plain,(
% 0.22/0.55    spl10_61 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).
% 0.22/0.55  fof(f701,plain,(
% 0.22/0.55    spl10_79 | spl10_80 | ~spl10_61 | ~spl10_75),
% 0.22/0.55    inference(avatar_split_clause,[],[f692,f670,f540,f698,f694])).
% 0.22/0.55  fof(f670,plain,(
% 0.22/0.55    spl10_75 <=> sK1 = k1_relset_1(sK1,k1_relat_1(sK4),sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).
% 0.22/0.55  fof(f692,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(sK4) | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | (~spl10_61 | ~spl10_75)),
% 0.22/0.55    inference(subsumption_resolution,[],[f549,f672])).
% 0.22/0.55  fof(f672,plain,(
% 0.22/0.55    sK1 = k1_relset_1(sK1,k1_relat_1(sK4),sK3) | ~spl10_75),
% 0.22/0.55    inference(avatar_component_clause,[],[f670])).
% 0.22/0.55  fof(f549,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(sK4) | sK1 != k1_relset_1(sK1,k1_relat_1(sK4),sK3) | v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~spl10_61),
% 0.22/0.55    inference(resolution,[],[f542,f90])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f43])).
% 0.22/0.55  fof(f682,plain,(
% 0.22/0.55    ~spl10_76 | ~spl10_1 | ~spl10_12 | ~spl10_16 | spl10_68),
% 0.22/0.55    inference(avatar_split_clause,[],[f611,f605,f256,f212,f109,f679])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    spl10_1 <=> v1_funct_1(sK4)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.55  fof(f212,plain,(
% 0.22/0.55    spl10_12 <=> v1_relat_1(sK4)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.22/0.55  fof(f256,plain,(
% 0.22/0.55    spl10_16 <=> v5_relat_1(sK4,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.22/0.55  fof(f605,plain,(
% 0.22/0.55    spl10_68 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).
% 0.22/0.55  fof(f611,plain,(
% 0.22/0.55    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | (~spl10_1 | ~spl10_12 | ~spl10_16 | spl10_68)),
% 0.22/0.55    inference(subsumption_resolution,[],[f610,f258])).
% 0.22/0.55  fof(f258,plain,(
% 0.22/0.55    v5_relat_1(sK4,sK0) | ~spl10_16),
% 0.22/0.55    inference(avatar_component_clause,[],[f256])).
% 0.22/0.55  fof(f610,plain,(
% 0.22/0.55    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v5_relat_1(sK4,sK0) | (~spl10_1 | ~spl10_12 | spl10_68)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f609])).
% 0.22/0.55  fof(f609,plain,(
% 0.22/0.55    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v5_relat_1(sK4,sK0) | (~spl10_1 | ~spl10_12 | spl10_68)),
% 0.22/0.55    inference(superposition,[],[f607,f235])).
% 0.22/0.55  fof(f235,plain,(
% 0.22/0.55    ( ! [X6,X7] : (k7_partfun1(X6,sK4,X7) = k1_funct_1(sK4,X7) | ~r2_hidden(X7,k1_relat_1(sK4)) | ~v5_relat_1(sK4,X6)) ) | (~spl10_1 | ~spl10_12)),
% 0.22/0.55    inference(subsumption_resolution,[],[f230,f111])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    v1_funct_1(sK4) | ~spl10_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f109])).
% 0.22/0.55  fof(f230,plain,(
% 0.22/0.55    ( ! [X6,X7] : (~v5_relat_1(sK4,X6) | ~v1_funct_1(sK4) | ~r2_hidden(X7,k1_relat_1(sK4)) | k7_partfun1(X6,sK4,X7) = k1_funct_1(sK4,X7)) ) | ~spl10_12),
% 0.22/0.55    inference(resolution,[],[f214,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.22/0.55  fof(f214,plain,(
% 0.22/0.55    v1_relat_1(sK4) | ~spl10_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f212])).
% 0.22/0.55  fof(f607,plain,(
% 0.22/0.55    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl10_68),
% 0.22/0.55    inference(avatar_component_clause,[],[f605])).
% 0.22/0.55  fof(f673,plain,(
% 0.22/0.55    spl10_75 | ~spl10_32 | ~spl10_61),
% 0.22/0.55    inference(avatar_split_clause,[],[f557,f540,f345,f670])).
% 0.22/0.55  fof(f345,plain,(
% 0.22/0.55    spl10_32 <=> sK1 = k1_relat_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 0.22/0.55  fof(f557,plain,(
% 0.22/0.55    sK1 = k1_relset_1(sK1,k1_relat_1(sK4),sK3) | (~spl10_32 | ~spl10_61)),
% 0.22/0.55    inference(forward_demodulation,[],[f546,f347])).
% 0.22/0.55  fof(f347,plain,(
% 0.22/0.55    sK1 = k1_relat_1(sK3) | ~spl10_32),
% 0.22/0.55    inference(avatar_component_clause,[],[f345])).
% 0.22/0.55  fof(f546,plain,(
% 0.22/0.55    k1_relat_1(sK3) = k1_relset_1(sK1,k1_relat_1(sK4),sK3) | ~spl10_61),
% 0.22/0.55    inference(resolution,[],[f542,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f608,plain,(
% 0.22/0.55    ~spl10_68 | spl10_13 | ~spl10_65),
% 0.22/0.55    inference(avatar_split_clause,[],[f589,f583,f217,f605])).
% 0.22/0.55  fof(f217,plain,(
% 0.22/0.55    spl10_13 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.22/0.55  fof(f583,plain,(
% 0.22/0.55    spl10_65 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).
% 0.22/0.55  fof(f589,plain,(
% 0.22/0.55    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl10_13 | ~spl10_65)),
% 0.22/0.55    inference(superposition,[],[f219,f585])).
% 0.22/0.55  fof(f585,plain,(
% 0.22/0.55    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl10_65),
% 0.22/0.55    inference(avatar_component_clause,[],[f583])).
% 0.22/0.55  fof(f219,plain,(
% 0.22/0.55    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl10_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f217])).
% 0.22/0.55  fof(f586,plain,(
% 0.22/0.55    spl10_65 | ~spl10_1 | ~spl10_2 | spl10_3 | ~spl10_4 | spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f498,f197,f145,f140,f134,f129,f124,f119,f114,f109,f583])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    spl10_3 <=> v1_xboole_0(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    spl10_4 <=> m1_subset_1(sK5,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    spl10_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.55  fof(f197,plain,(
% 0.22/0.55    spl10_11 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.22/0.55  fof(f498,plain,(
% 0.22/0.55    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl10_1 | ~spl10_2 | spl10_3 | ~spl10_4 | spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_11)),
% 0.22/0.55    inference(resolution,[],[f210,f126])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    m1_subset_1(sK5,sK1) | ~spl10_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f124])).
% 0.22/0.55  fof(f210,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl10_1 | ~spl10_2 | spl10_3 | spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f209,f131])).
% 0.22/0.55  fof(f209,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl10_1 | ~spl10_2 | spl10_3 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f208,f121])).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    ~v1_xboole_0(sK2) | spl10_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f119])).
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl10_1 | ~spl10_2 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f207,f142])).
% 0.22/0.55  fof(f142,plain,(
% 0.22/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl10_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f140])).
% 0.22/0.55  fof(f207,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl10_1 | ~spl10_2 | ~spl10_6 | ~spl10_8 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f206,f111])).
% 0.22/0.55  fof(f206,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl10_2 | ~spl10_6 | ~spl10_8 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f205,f147])).
% 0.22/0.55  fof(f205,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl10_2 | ~spl10_6 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f204,f136])).
% 0.22/0.55  fof(f204,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl10_2 | ~spl10_11)),
% 0.22/0.55    inference(subsumption_resolution,[],[f201,f116])).
% 0.22/0.55  fof(f201,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | ~spl10_11),
% 0.22/0.55    inference(resolution,[],[f199,f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | v1_xboole_0(X2) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.22/0.55    inference(flattening,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.55  fof(f199,plain,(
% 0.22/0.55    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl10_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f197])).
% 0.22/0.55  fof(f580,plain,(
% 0.22/0.55    spl10_64 | ~spl10_14 | ~spl10_62),
% 0.22/0.55    inference(avatar_split_clause,[],[f567,f562,f222,f577])).
% 0.22/0.55  fof(f562,plain,(
% 0.22/0.55    spl10_62 <=> v5_relat_1(sK3,k1_relat_1(sK4))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).
% 0.22/0.55  fof(f567,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl10_14 | ~spl10_62)),
% 0.22/0.55    inference(resolution,[],[f564,f241])).
% 0.22/0.55  fof(f241,plain,(
% 0.22/0.55    ( ! [X5] : (~v5_relat_1(sK3,X5) | r1_tarski(k2_relat_1(sK3),X5)) ) | ~spl10_14),
% 0.22/0.55    inference(resolution,[],[f224,f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.55  fof(f564,plain,(
% 0.22/0.55    v5_relat_1(sK3,k1_relat_1(sK4)) | ~spl10_62),
% 0.22/0.55    inference(avatar_component_clause,[],[f562])).
% 0.22/0.55  fof(f565,plain,(
% 0.22/0.55    spl10_62 | ~spl10_61),
% 0.22/0.55    inference(avatar_split_clause,[],[f548,f540,f562])).
% 0.22/0.55  fof(f548,plain,(
% 0.22/0.55    v5_relat_1(sK3,k1_relat_1(sK4)) | ~spl10_61),
% 0.22/0.55    inference(resolution,[],[f542,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.55  fof(f544,plain,(
% 0.22/0.55    spl10_61 | ~spl10_2 | ~spl10_6 | ~spl10_8 | ~spl10_11 | ~spl10_21 | spl10_31),
% 0.22/0.55    inference(avatar_split_clause,[],[f489,f340,f285,f197,f145,f134,f114,f540])).
% 0.22/0.55  fof(f285,plain,(
% 0.22/0.55    spl10_21 <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.22/0.55  fof(f489,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | (~spl10_2 | ~spl10_6 | ~spl10_8 | ~spl10_11 | ~spl10_21 | spl10_31)),
% 0.22/0.55    inference(forward_demodulation,[],[f488,f287])).
% 0.22/0.55  fof(f287,plain,(
% 0.22/0.55    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl10_21),
% 0.22/0.55    inference(avatar_component_clause,[],[f285])).
% 0.22/0.55  fof(f488,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relset_1(sK2,sK0,sK4)))) | (~spl10_2 | ~spl10_6 | ~spl10_8 | ~spl10_11 | spl10_31)),
% 0.22/0.55    inference(resolution,[],[f482,f199])).
% 0.22/0.55  fof(f482,plain,(
% 0.22/0.55    ( ! [X2] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) ) | (~spl10_2 | ~spl10_6 | ~spl10_8 | spl10_31)),
% 0.22/0.55    inference(subsumption_resolution,[],[f195,f341])).
% 0.22/0.55  fof(f195,plain,(
% 0.22/0.55    ( ! [X2] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) ) | (~spl10_2 | ~spl10_6 | ~spl10_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f194,f116])).
% 0.22/0.55  fof(f194,plain,(
% 0.22/0.55    ( ! [X2] : (~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) ) | (~spl10_6 | ~spl10_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f185,f136])).
% 0.22/0.55  fof(f185,plain,(
% 0.22/0.55    ( ! [X2] : (~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X2) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))) ) | ~spl10_8),
% 0.22/0.55    inference(resolution,[],[f147,f97])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f518,plain,(
% 0.22/0.55    ~spl10_55 | spl10_56 | ~spl10_37),
% 0.22/0.55    inference(avatar_split_clause,[],[f408,f404,f516,f512])).
% 0.22/0.55  fof(f404,plain,(
% 0.22/0.55    spl10_37 <=> m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(k1_relat_1(sK4)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 0.22/0.55  fof(f408,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) | ~v1_xboole_0(k1_relat_1(sK4))) ) | ~spl10_37),
% 0.22/0.55    inference(resolution,[],[f406,f92])).
% 0.22/0.55  fof(f406,plain,(
% 0.22/0.55    m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(k1_relat_1(sK4))) | ~spl10_37),
% 0.22/0.55    inference(avatar_component_clause,[],[f404])).
% 0.22/0.55  fof(f407,plain,(
% 0.22/0.55    spl10_37 | ~spl10_11 | ~spl10_21),
% 0.22/0.55    inference(avatar_split_clause,[],[f397,f285,f197,f404])).
% 0.22/0.55  fof(f397,plain,(
% 0.22/0.55    m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(k1_relat_1(sK4))) | (~spl10_11 | ~spl10_21)),
% 0.22/0.55    inference(forward_demodulation,[],[f203,f287])).
% 0.22/0.55  fof(f203,plain,(
% 0.22/0.55    m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(k1_relset_1(sK2,sK0,sK4))) | ~spl10_11),
% 0.22/0.55    inference(resolution,[],[f199,f78])).
% 0.22/0.55  fof(f381,plain,(
% 0.22/0.55    spl10_3 | ~spl10_31),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f380])).
% 0.22/0.55  fof(f380,plain,(
% 0.22/0.55    $false | (spl10_3 | ~spl10_31)),
% 0.22/0.55    inference(subsumption_resolution,[],[f363,f59])).
% 0.22/0.55  fof(f363,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_xboole_0) | (spl10_3 | ~spl10_31)),
% 0.22/0.55    inference(superposition,[],[f121,f342])).
% 0.22/0.55  fof(f342,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | ~spl10_31),
% 0.22/0.55    inference(avatar_component_clause,[],[f340])).
% 0.22/0.55  fof(f354,plain,(
% 0.22/0.55    spl10_32 | ~spl10_25 | ~spl10_30),
% 0.22/0.55    inference(avatar_split_clause,[],[f348,f336,f303,f345])).
% 0.22/0.55  fof(f303,plain,(
% 0.22/0.55    spl10_25 <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.22/0.55  fof(f336,plain,(
% 0.22/0.55    spl10_30 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.22/0.55  fof(f348,plain,(
% 0.22/0.55    sK1 = k1_relat_1(sK3) | (~spl10_25 | ~spl10_30)),
% 0.22/0.55    inference(superposition,[],[f338,f305])).
% 0.22/0.55  fof(f305,plain,(
% 0.22/0.55    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl10_25),
% 0.22/0.55    inference(avatar_component_clause,[],[f303])).
% 0.22/0.55  fof(f338,plain,(
% 0.22/0.55    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl10_30),
% 0.22/0.55    inference(avatar_component_clause,[],[f336])).
% 0.22/0.55  fof(f343,plain,(
% 0.22/0.55    spl10_30 | spl10_31 | ~spl10_6 | ~spl10_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f189,f145,f134,f340,f336])).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | (~spl10_6 | ~spl10_8)),
% 0.22/0.55    inference(subsumption_resolution,[],[f182,f136])).
% 0.22/0.55  fof(f182,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~spl10_8),
% 0.22/0.55    inference(resolution,[],[f147,f91])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f43])).
% 0.22/0.55  fof(f306,plain,(
% 0.22/0.55    spl10_25 | ~spl10_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f178,f145,f303])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl10_8),
% 0.22/0.55    inference(resolution,[],[f147,f83])).
% 0.22/0.55  fof(f288,plain,(
% 0.22/0.55    spl10_21 | ~spl10_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f159,f140,f285])).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl10_7),
% 0.22/0.55    inference(resolution,[],[f142,f83])).
% 0.22/0.55  fof(f259,plain,(
% 0.22/0.55    spl10_16 | ~spl10_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f161,f140,f256])).
% 0.22/0.55  fof(f161,plain,(
% 0.22/0.55    v5_relat_1(sK4,sK0) | ~spl10_7),
% 0.22/0.55    inference(resolution,[],[f142,f85])).
% 0.22/0.55  fof(f225,plain,(
% 0.22/0.55    spl10_14 | ~spl10_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f177,f145,f222])).
% 0.22/0.55  fof(f177,plain,(
% 0.22/0.55    v1_relat_1(sK3) | ~spl10_8),
% 0.22/0.55    inference(resolution,[],[f147,f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f220,plain,(
% 0.22/0.55    ~spl10_13),
% 0.22/0.55    inference(avatar_split_clause,[],[f52,f217])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.22/0.55    inference(flattening,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.55    inference(negated_conjecture,[],[f21])).
% 0.22/0.55  fof(f21,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.22/0.55  fof(f215,plain,(
% 0.22/0.55    spl10_12 | ~spl10_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f158,f140,f212])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    v1_relat_1(sK4) | ~spl10_7),
% 0.22/0.55    inference(resolution,[],[f142,f82])).
% 0.22/0.55  fof(f200,plain,(
% 0.22/0.55    spl10_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f50,f197])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    spl10_5 | ~spl10_10),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f175])).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    $false | (spl10_5 | ~spl10_10)),
% 0.22/0.55    inference(subsumption_resolution,[],[f174,f131])).
% 0.22/0.55  fof(f174,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | ~spl10_10),
% 0.22/0.55    inference(resolution,[],[f156,f62])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    v1_xboole_0(sK1) | ~spl10_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f154])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    spl10_9 | spl10_10 | ~spl10_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f138,f124,f154,f150])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    v1_xboole_0(sK1) | r2_hidden(sK5,sK1) | ~spl10_4),
% 0.22/0.55    inference(resolution,[],[f126,f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    spl10_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f57,f145])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    spl10_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f54,f140])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    spl10_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f56,f134])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    ~spl10_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f51,f129])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    k1_xboole_0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    spl10_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f49,f124])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    m1_subset_1(sK5,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    ~spl10_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f58,f119])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ~v1_xboole_0(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    spl10_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f55,f114])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    v1_funct_1(sK3)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    spl10_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f53,f109])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    v1_funct_1(sK4)),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (32551)------------------------------
% 0.22/0.55  % (32551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32551)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (32551)Memory used [KB]: 11513
% 0.22/0.55  % (32551)Time elapsed: 0.116 s
% 0.22/0.55  % (32551)------------------------------
% 0.22/0.55  % (32551)------------------------------
% 1.56/0.55  % (32547)Success in time 0.192 s
%------------------------------------------------------------------------------
