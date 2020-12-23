%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:06 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 409 expanded)
%              Number of leaves         :   51 ( 195 expanded)
%              Depth                    :    8
%              Number of atoms          :  640 (1222 expanded)
%              Number of equality atoms :   91 ( 221 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1096,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f115,f120,f130,f143,f196,f206,f213,f233,f239,f263,f268,f277,f282,f382,f392,f397,f429,f439,f546,f558,f605,f616,f622,f623,f699,f709,f764,f804,f817,f823,f855,f871,f900,f962,f970,f1016,f1030,f1067])).

fof(f1067,plain,
    ( ~ spl5_87
    | spl5_6
    | ~ spl5_44
    | ~ spl5_48
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f1026,f814,f436,f416,f132,f771])).

fof(f771,plain,
    ( spl5_87
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f132,plain,
    ( spl5_6
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f416,plain,
    ( spl5_44
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f436,plain,
    ( spl5_48
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f814,plain,
    ( spl5_94
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f1026,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl5_6
    | ~ spl5_44
    | ~ spl5_48
    | ~ spl5_94 ),
    inference(forward_demodulation,[],[f1025,f816])).

% (9111)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f816,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f814])).

fof(f1025,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl5_6
    | ~ spl5_44
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f1024,f438])).

fof(f438,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f436])).

fof(f1024,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl5_6
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f1023,f103])).

fof(f103,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1023,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl5_6
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f134,f417])).

fof(f417,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f416])).

fof(f134,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f1030,plain,(
    spl5_87 ),
    inference(avatar_contradiction_clause,[],[f1027])).

fof(f1027,plain,
    ( $false
    | spl5_87 ),
    inference(unit_resulting_resolution,[],[f59,f773])).

fof(f773,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl5_87 ),
    inference(avatar_component_clause,[],[f771])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1016,plain,
    ( ~ spl5_73
    | ~ spl5_97
    | spl5_104
    | ~ spl5_105 ),
    inference(avatar_contradiction_clause,[],[f1015])).

fof(f1015,plain,
    ( $false
    | ~ spl5_73
    | ~ spl5_97
    | spl5_104
    | ~ spl5_105 ),
    inference(unit_resulting_resolution,[],[f698,f854,f961,f59,f967,f146])).

fof(f146,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f105,f103])).

fof(f105,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_tarski(X1,X2)
      | v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 != X0
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f967,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_105 ),
    inference(avatar_component_clause,[],[f965])).

fof(f965,plain,
    ( spl5_105
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).

fof(f961,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl5_104 ),
    inference(avatar_component_clause,[],[f959])).

fof(f959,plain,
    ( spl5_104
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f854,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl5_97 ),
    inference(avatar_component_clause,[],[f852])).

fof(f852,plain,
    ( spl5_97
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f698,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f696])).

fof(f696,plain,
    ( spl5_73
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f970,plain,
    ( spl5_105
    | ~ spl5_44
    | ~ spl5_99 ),
    inference(avatar_split_clause,[],[f969,f868,f416,f965])).

fof(f868,plain,
    ( spl5_99
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).

fof(f969,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_44
    | ~ spl5_99 ),
    inference(forward_demodulation,[],[f870,f417])).

fof(f870,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl5_99 ),
    inference(avatar_component_clause,[],[f868])).

% (9110)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f962,plain,
    ( ~ spl5_104
    | ~ spl5_44
    | spl5_101 ),
    inference(avatar_split_clause,[],[f957,f897,f416,f959])).

fof(f897,plain,
    ( spl5_101
  <=> v1_funct_2(k1_xboole_0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f957,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl5_44
    | spl5_101 ),
    inference(forward_demodulation,[],[f899,f417])).

fof(f899,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,sK0)
    | spl5_101 ),
    inference(avatar_component_clause,[],[f897])).

fof(f900,plain,
    ( ~ spl5_101
    | spl5_75
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f895,f814,f706,f897])).

fof(f706,plain,
    ( spl5_75
  <=> v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f895,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,sK0)
    | spl5_75
    | ~ spl5_94 ),
    inference(forward_demodulation,[],[f708,f816])).

fof(f708,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0)
    | spl5_75 ),
    inference(avatar_component_clause,[],[f706])).

fof(f871,plain,
    ( spl5_99
    | ~ spl5_85
    | ~ spl5_95 ),
    inference(avatar_split_clause,[],[f866,f820,f761,f868])).

fof(f761,plain,
    ( spl5_85
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f820,plain,
    ( spl5_95
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).

fof(f866,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl5_85
    | ~ spl5_95 ),
    inference(forward_demodulation,[],[f763,f822])).

fof(f822,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_95 ),
    inference(avatar_component_clause,[],[f820])).

fof(f763,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK1)
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f761])).

fof(f855,plain,
    ( spl5_97
    | ~ spl5_92
    | ~ spl5_95 ),
    inference(avatar_split_clause,[],[f850,f820,f801,f852])).

fof(f801,plain,
    ( spl5_92
  <=> r1_tarski(k1_relat_1(k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f850,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ spl5_92
    | ~ spl5_95 ),
    inference(forward_demodulation,[],[f803,f822])).

fof(f803,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f801])).

fof(f823,plain,
    ( spl5_95
    | ~ spl5_23
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f818,f436,f246,f820])).

fof(f246,plain,
    ( spl5_23
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f818,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_23
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f248,f438])).

fof(f248,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f246])).

fof(f817,plain,
    ( spl5_94
    | ~ spl5_25
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f812,f436,f255,f814])).

fof(f255,plain,
    ( spl5_25
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f812,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl5_25
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f257,f438])).

fof(f257,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f255])).

fof(f804,plain,
    ( spl5_92
    | ~ spl5_48
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f670,f568,f436,f801])).

fof(f568,plain,
    ( spl5_65
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f670,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK0)
    | ~ spl5_48
    | ~ spl5_65 ),
    inference(backward_demodulation,[],[f570,f438])).

fof(f570,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f568])).

fof(f764,plain,
    ( spl5_85
    | ~ spl5_46
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f651,f436,f426,f761])).

fof(f426,plain,
    ( spl5_46
  <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f651,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK1)
    | ~ spl5_46
    | ~ spl5_48 ),
    inference(backward_demodulation,[],[f428,f438])).

fof(f428,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f426])).

fof(f709,plain,
    ( ~ spl5_75
    | spl5_7
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f633,f436,f136,f706])).

fof(f136,plain,
    ( spl5_7
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f633,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0)
    | spl5_7
    | ~ spl5_48 ),
    inference(backward_demodulation,[],[f138,f438])).

fof(f138,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f699,plain,
    ( spl5_73
    | ~ spl5_5
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f631,f436,f127,f696])).

fof(f127,plain,
    ( spl5_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f631,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_5
    | ~ spl5_48 ),
    inference(backward_demodulation,[],[f129,f438])).

fof(f129,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f623,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | sK1 != k2_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f622,plain,
    ( ~ spl5_3
    | spl5_69 ),
    inference(avatar_contradiction_clause,[],[f621])).

fof(f621,plain,
    ( $false
    | ~ spl5_3
    | spl5_69 ),
    inference(subsumption_resolution,[],[f119,f618])).

fof(f618,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | spl5_69 ),
    inference(resolution,[],[f615,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f615,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl5_69 ),
    inference(avatar_component_clause,[],[f613])).

fof(f613,plain,
    ( spl5_69
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f119,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f616,plain,
    ( ~ spl5_69
    | ~ spl5_15
    | spl5_65 ),
    inference(avatar_split_clause,[],[f610,f568,f193,f613])).

fof(f193,plain,
    ( spl5_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f610,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl5_65 ),
    inference(resolution,[],[f569,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f569,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl5_65 ),
    inference(avatar_component_clause,[],[f568])).

fof(f605,plain,
    ( ~ spl5_41
    | ~ spl5_65
    | spl5_23
    | ~ spl5_40
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f602,f544,f389,f246,f568,f394])).

fof(f394,plain,
    ( spl5_41
  <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f389,plain,
    ( spl5_40
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f544,plain,
    ( spl5_61
  <=> ! [X0] :
        ( ~ v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f602,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl5_40
    | ~ spl5_61 ),
    inference(resolution,[],[f545,f391])).

fof(f391,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f389])).

fof(f545,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK0)
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,X0) )
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f544])).

fof(f558,plain,
    ( ~ spl5_8
    | spl5_61
    | spl5_7 ),
    inference(avatar_split_clause,[],[f556,f136,f544,f140])).

fof(f140,plain,
    ( spl5_8
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f556,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | spl5_7 ),
    inference(resolution,[],[f138,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f546,plain,
    ( ~ spl5_8
    | spl5_61
    | spl5_6 ),
    inference(avatar_split_clause,[],[f536,f132,f544,f140])).

fof(f536,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | spl5_6 ),
    inference(resolution,[],[f96,f134])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f439,plain,
    ( spl5_48
    | ~ spl5_15
    | ~ spl5_44
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f414,f379,f416,f193,f436])).

fof(f379,plain,
    ( spl5_39
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f414,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl5_39 ),
    inference(superposition,[],[f61,f381])).

fof(f381,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f379])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f429,plain,
    ( ~ spl5_15
    | ~ spl5_5
    | spl5_46
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f411,f379,f426,f127,f193])).

fof(f411,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_39 ),
    inference(superposition,[],[f64,f381])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f397,plain,
    ( spl5_41
    | ~ spl5_21
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f385,f379,f236,f394])).

fof(f236,plain,
    ( spl5_21
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f385,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl5_21
    | ~ spl5_39 ),
    inference(backward_demodulation,[],[f238,f381])).

fof(f238,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f236])).

fof(f392,plain,
    ( spl5_40
    | ~ spl5_20
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f384,f379,f230,f389])).

fof(f230,plain,
    ( spl5_20
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f384,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl5_20
    | ~ spl5_39 ),
    inference(backward_demodulation,[],[f232,f381])).

fof(f232,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f230])).

fof(f382,plain,
    ( spl5_39
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f377,f117,f107,f379])).

fof(f107,plain,
    ( spl5_1
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f377,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f367,f109])).

fof(f109,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f367,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f89,f119])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f282,plain,
    ( spl5_25
    | ~ spl5_19
    | ~ spl5_23
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f273,f210,f246,f226,f255])).

fof(f226,plain,
    ( spl5_19
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f210,plain,
    ( spl5_17
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f273,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl5_17 ),
    inference(superposition,[],[f61,f212])).

fof(f212,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f210])).

fof(f277,plain,
    ( ~ spl5_19
    | ~ spl5_23
    | spl5_22
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f276,f210,f189,f242,f246,f226])).

fof(f242,plain,
    ( spl5_22
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f189,plain,
    ( spl5_14
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f276,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f271,f191])).

fof(f191,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f189])).

fof(f271,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_17 ),
    inference(superposition,[],[f62,f212])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f268,plain,
    ( ~ spl5_15
    | ~ spl5_5
    | spl5_8 ),
    inference(avatar_split_clause,[],[f265,f140,f127,f193])).

fof(f265,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_8 ),
    inference(resolution,[],[f142,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f142,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f263,plain,
    ( ~ spl5_15
    | ~ spl5_5
    | spl5_19 ),
    inference(avatar_split_clause,[],[f260,f226,f127,f193])).

fof(f260,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_19 ),
    inference(resolution,[],[f228,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f228,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f226])).

fof(f239,plain,
    ( ~ spl5_19
    | ~ spl5_8
    | spl5_21
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f234,f210,f189,f236,f140,f226])).

fof(f234,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f220,f212])).

fof(f220,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_14 ),
    inference(superposition,[],[f64,f191])).

fof(f233,plain,
    ( ~ spl5_19
    | ~ spl5_8
    | spl5_20
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f224,f210,f189,f230,f140,f226])).

fof(f224,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f219,f212])).

fof(f219,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_14 ),
    inference(superposition,[],[f65,f191])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f213,plain,
    ( spl5_17
    | ~ spl5_15
    | ~ spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f207,f112,f127,f193,f210])).

fof(f112,plain,
    ( spl5_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f207,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f69,f114])).

fof(f114,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f206,plain,
    ( ~ spl5_3
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl5_3
    | spl5_15 ),
    inference(subsumption_resolution,[],[f119,f203])).

fof(f203,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_15 ),
    inference(resolution,[],[f195,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f195,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f196,plain,
    ( spl5_14
    | ~ spl5_15
    | ~ spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f186,f112,f127,f193,f189])).

fof(f186,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f68,f114])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f143,plain,
    ( ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f53,f140,f136,f132])).

fof(f53,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f130,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f54,f127])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f120,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f115,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f57,f112])).

fof(f57,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f110,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f58,f107])).

fof(f58,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:10:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (9132)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (9124)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (9115)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (9116)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.50  % (9113)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (9109)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (9120)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (9133)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (9123)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (9130)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (9129)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (9117)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (9131)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (9121)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (9114)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (9115)Refutation not found, incomplete strategy% (9115)------------------------------
% 0.22/0.52  % (9115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9115)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9115)Memory used [KB]: 10746
% 0.22/0.52  % (9115)Time elapsed: 0.106 s
% 0.22/0.52  % (9115)------------------------------
% 0.22/0.52  % (9115)------------------------------
% 0.22/0.52  % (9112)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (9125)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (9134)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.36/0.53  % (9122)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.36/0.54  % (9127)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.36/0.54  % (9124)Refutation found. Thanks to Tanya!
% 1.36/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f1096,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(avatar_sat_refutation,[],[f110,f115,f120,f130,f143,f196,f206,f213,f233,f239,f263,f268,f277,f282,f382,f392,f397,f429,f439,f546,f558,f605,f616,f622,f623,f699,f709,f764,f804,f817,f823,f855,f871,f900,f962,f970,f1016,f1030,f1067])).
% 1.36/0.54  fof(f1067,plain,(
% 1.36/0.54    ~spl5_87 | spl5_6 | ~spl5_44 | ~spl5_48 | ~spl5_94),
% 1.36/0.54    inference(avatar_split_clause,[],[f1026,f814,f436,f416,f132,f771])).
% 1.36/0.54  fof(f771,plain,(
% 1.36/0.54    spl5_87 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 1.36/0.54  fof(f132,plain,(
% 1.36/0.54    spl5_6 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.36/0.54  fof(f416,plain,(
% 1.36/0.54    spl5_44 <=> k1_xboole_0 = sK1),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 1.36/0.54  fof(f436,plain,(
% 1.36/0.54    spl5_48 <=> k1_xboole_0 = sK2),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 1.36/0.54  fof(f814,plain,(
% 1.36/0.54    spl5_94 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 1.36/0.54  fof(f1026,plain,(
% 1.36/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl5_6 | ~spl5_44 | ~spl5_48 | ~spl5_94)),
% 1.36/0.54    inference(forward_demodulation,[],[f1025,f816])).
% 1.36/0.54  % (9111)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.36/0.54  fof(f816,plain,(
% 1.36/0.54    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl5_94),
% 1.36/0.54    inference(avatar_component_clause,[],[f814])).
% 1.36/0.54  fof(f1025,plain,(
% 1.36/0.54    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl5_6 | ~spl5_44 | ~spl5_48)),
% 1.36/0.54    inference(forward_demodulation,[],[f1024,f438])).
% 1.36/0.54  fof(f438,plain,(
% 1.36/0.54    k1_xboole_0 = sK2 | ~spl5_48),
% 1.36/0.54    inference(avatar_component_clause,[],[f436])).
% 1.36/0.54  fof(f1024,plain,(
% 1.36/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl5_6 | ~spl5_44)),
% 1.36/0.54    inference(forward_demodulation,[],[f1023,f103])).
% 1.36/0.54  fof(f103,plain,(
% 1.36/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.36/0.54    inference(equality_resolution,[],[f86])).
% 1.36/0.54  fof(f86,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.36/0.54  fof(f1023,plain,(
% 1.36/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl5_6 | ~spl5_44)),
% 1.36/0.54    inference(forward_demodulation,[],[f134,f417])).
% 1.36/0.54  fof(f417,plain,(
% 1.36/0.54    k1_xboole_0 = sK1 | ~spl5_44),
% 1.36/0.54    inference(avatar_component_clause,[],[f416])).
% 1.36/0.54  fof(f134,plain,(
% 1.36/0.54    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_6),
% 1.36/0.54    inference(avatar_component_clause,[],[f132])).
% 1.36/0.54  fof(f1030,plain,(
% 1.36/0.54    spl5_87),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f1027])).
% 1.36/0.54  fof(f1027,plain,(
% 1.36/0.54    $false | spl5_87),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f59,f773])).
% 1.36/0.54  fof(f773,plain,(
% 1.36/0.54    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl5_87),
% 1.36/0.54    inference(avatar_component_clause,[],[f771])).
% 1.36/0.54  fof(f59,plain,(
% 1.36/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.36/0.54  fof(f1016,plain,(
% 1.36/0.54    ~spl5_73 | ~spl5_97 | spl5_104 | ~spl5_105),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f1015])).
% 1.36/0.54  fof(f1015,plain,(
% 1.36/0.54    $false | (~spl5_73 | ~spl5_97 | spl5_104 | ~spl5_105)),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f698,f854,f961,f59,f967,f146])).
% 1.36/0.54  fof(f146,plain,(
% 1.36/0.54    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f105,f103])).
% 1.36/0.54  fof(f105,plain,(
% 1.36/0.54    ( ! [X2,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_tarski(X1,X2) | v1_funct_2(X3,k1_xboole_0,X2)) )),
% 1.36/0.54    inference(equality_resolution,[],[f93])).
% 1.36/0.54  fof(f93,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 != X0 | v1_funct_2(X3,X0,X2)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f52])).
% 1.36/0.54  fof(f52,plain,(
% 1.36/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.36/0.54    inference(flattening,[],[f51])).
% 1.36/0.54  fof(f51,plain,(
% 1.36/0.54    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.36/0.54    inference(ennf_transformation,[],[f21])).
% 1.36/0.54  fof(f21,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 1.36/0.54  fof(f967,plain,(
% 1.36/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl5_105),
% 1.36/0.54    inference(avatar_component_clause,[],[f965])).
% 1.36/0.54  fof(f965,plain,(
% 1.36/0.54    spl5_105 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_105])])).
% 1.36/0.54  fof(f961,plain,(
% 1.36/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | spl5_104),
% 1.36/0.54    inference(avatar_component_clause,[],[f959])).
% 1.36/0.54  fof(f959,plain,(
% 1.36/0.54    spl5_104 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).
% 1.36/0.54  fof(f854,plain,(
% 1.36/0.54    r1_tarski(k1_xboole_0,sK0) | ~spl5_97),
% 1.36/0.54    inference(avatar_component_clause,[],[f852])).
% 1.36/0.54  fof(f852,plain,(
% 1.36/0.54    spl5_97 <=> r1_tarski(k1_xboole_0,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 1.36/0.54  fof(f698,plain,(
% 1.36/0.54    v1_funct_1(k1_xboole_0) | ~spl5_73),
% 1.36/0.54    inference(avatar_component_clause,[],[f696])).
% 1.36/0.54  fof(f696,plain,(
% 1.36/0.54    spl5_73 <=> v1_funct_1(k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 1.36/0.54  fof(f970,plain,(
% 1.36/0.54    spl5_105 | ~spl5_44 | ~spl5_99),
% 1.36/0.54    inference(avatar_split_clause,[],[f969,f868,f416,f965])).
% 1.36/0.54  fof(f868,plain,(
% 1.36/0.54    spl5_99 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_99])])).
% 1.36/0.54  fof(f969,plain,(
% 1.36/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_44 | ~spl5_99)),
% 1.36/0.54    inference(forward_demodulation,[],[f870,f417])).
% 1.36/0.54  fof(f870,plain,(
% 1.36/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | ~spl5_99),
% 1.36/0.54    inference(avatar_component_clause,[],[f868])).
% 1.36/0.54  % (9110)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.54  fof(f962,plain,(
% 1.36/0.54    ~spl5_104 | ~spl5_44 | spl5_101),
% 1.36/0.54    inference(avatar_split_clause,[],[f957,f897,f416,f959])).
% 1.36/0.54  fof(f897,plain,(
% 1.36/0.54    spl5_101 <=> v1_funct_2(k1_xboole_0,sK1,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).
% 1.36/0.54  fof(f957,plain,(
% 1.36/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (~spl5_44 | spl5_101)),
% 1.36/0.54    inference(forward_demodulation,[],[f899,f417])).
% 1.36/0.54  fof(f899,plain,(
% 1.36/0.54    ~v1_funct_2(k1_xboole_0,sK1,sK0) | spl5_101),
% 1.36/0.54    inference(avatar_component_clause,[],[f897])).
% 1.36/0.54  fof(f900,plain,(
% 1.36/0.54    ~spl5_101 | spl5_75 | ~spl5_94),
% 1.36/0.54    inference(avatar_split_clause,[],[f895,f814,f706,f897])).
% 1.36/0.54  fof(f706,plain,(
% 1.36/0.54    spl5_75 <=> v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 1.36/0.54  fof(f895,plain,(
% 1.36/0.54    ~v1_funct_2(k1_xboole_0,sK1,sK0) | (spl5_75 | ~spl5_94)),
% 1.36/0.54    inference(forward_demodulation,[],[f708,f816])).
% 1.36/0.54  fof(f708,plain,(
% 1.36/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0) | spl5_75),
% 1.36/0.54    inference(avatar_component_clause,[],[f706])).
% 1.36/0.54  fof(f871,plain,(
% 1.36/0.54    spl5_99 | ~spl5_85 | ~spl5_95),
% 1.36/0.54    inference(avatar_split_clause,[],[f866,f820,f761,f868])).
% 1.36/0.54  fof(f761,plain,(
% 1.36/0.54    spl5_85 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 1.36/0.54  fof(f820,plain,(
% 1.36/0.54    spl5_95 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_95])])).
% 1.36/0.54  fof(f866,plain,(
% 1.36/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (~spl5_85 | ~spl5_95)),
% 1.36/0.54    inference(forward_demodulation,[],[f763,f822])).
% 1.36/0.54  fof(f822,plain,(
% 1.36/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_95),
% 1.36/0.54    inference(avatar_component_clause,[],[f820])).
% 1.36/0.54  fof(f763,plain,(
% 1.36/0.54    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK1) | ~spl5_85),
% 1.36/0.54    inference(avatar_component_clause,[],[f761])).
% 1.36/0.54  fof(f855,plain,(
% 1.36/0.54    spl5_97 | ~spl5_92 | ~spl5_95),
% 1.36/0.54    inference(avatar_split_clause,[],[f850,f820,f801,f852])).
% 1.36/0.54  fof(f801,plain,(
% 1.36/0.54    spl5_92 <=> r1_tarski(k1_relat_1(k1_xboole_0),sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 1.36/0.54  fof(f850,plain,(
% 1.36/0.54    r1_tarski(k1_xboole_0,sK0) | (~spl5_92 | ~spl5_95)),
% 1.36/0.54    inference(forward_demodulation,[],[f803,f822])).
% 1.36/0.54  fof(f803,plain,(
% 1.36/0.54    r1_tarski(k1_relat_1(k1_xboole_0),sK0) | ~spl5_92),
% 1.36/0.54    inference(avatar_component_clause,[],[f801])).
% 1.36/0.54  fof(f823,plain,(
% 1.36/0.54    spl5_95 | ~spl5_23 | ~spl5_48),
% 1.36/0.54    inference(avatar_split_clause,[],[f818,f436,f246,f820])).
% 1.36/0.54  fof(f246,plain,(
% 1.36/0.54    spl5_23 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.36/0.54  fof(f818,plain,(
% 1.36/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_23 | ~spl5_48)),
% 1.36/0.54    inference(forward_demodulation,[],[f248,f438])).
% 1.36/0.54  fof(f248,plain,(
% 1.36/0.54    k1_xboole_0 = k1_relat_1(sK2) | ~spl5_23),
% 1.36/0.54    inference(avatar_component_clause,[],[f246])).
% 1.36/0.54  fof(f817,plain,(
% 1.36/0.54    spl5_94 | ~spl5_25 | ~spl5_48),
% 1.36/0.54    inference(avatar_split_clause,[],[f812,f436,f255,f814])).
% 1.36/0.54  fof(f255,plain,(
% 1.36/0.54    spl5_25 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.36/0.54  fof(f812,plain,(
% 1.36/0.54    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl5_25 | ~spl5_48)),
% 1.36/0.54    inference(forward_demodulation,[],[f257,f438])).
% 1.36/0.54  fof(f257,plain,(
% 1.36/0.54    k1_xboole_0 = k2_funct_1(sK2) | ~spl5_25),
% 1.36/0.54    inference(avatar_component_clause,[],[f255])).
% 1.36/0.54  fof(f804,plain,(
% 1.36/0.54    spl5_92 | ~spl5_48 | ~spl5_65),
% 1.36/0.54    inference(avatar_split_clause,[],[f670,f568,f436,f801])).
% 1.36/0.54  fof(f568,plain,(
% 1.36/0.54    spl5_65 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 1.36/0.54  fof(f670,plain,(
% 1.36/0.54    r1_tarski(k1_relat_1(k1_xboole_0),sK0) | (~spl5_48 | ~spl5_65)),
% 1.36/0.54    inference(backward_demodulation,[],[f570,f438])).
% 1.36/0.54  fof(f570,plain,(
% 1.36/0.54    r1_tarski(k1_relat_1(sK2),sK0) | ~spl5_65),
% 1.36/0.54    inference(avatar_component_clause,[],[f568])).
% 1.36/0.54  fof(f764,plain,(
% 1.36/0.54    spl5_85 | ~spl5_46 | ~spl5_48),
% 1.36/0.54    inference(avatar_split_clause,[],[f651,f436,f426,f761])).
% 1.36/0.54  fof(f426,plain,(
% 1.36/0.54    spl5_46 <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 1.36/0.54  fof(f651,plain,(
% 1.36/0.54    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),sK1) | (~spl5_46 | ~spl5_48)),
% 1.36/0.54    inference(backward_demodulation,[],[f428,f438])).
% 1.36/0.54  fof(f428,plain,(
% 1.36/0.54    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~spl5_46),
% 1.36/0.54    inference(avatar_component_clause,[],[f426])).
% 1.36/0.54  fof(f709,plain,(
% 1.36/0.54    ~spl5_75 | spl5_7 | ~spl5_48),
% 1.36/0.54    inference(avatar_split_clause,[],[f633,f436,f136,f706])).
% 1.36/0.54  fof(f136,plain,(
% 1.36/0.54    spl5_7 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.36/0.54  fof(f633,plain,(
% 1.36/0.54    ~v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0) | (spl5_7 | ~spl5_48)),
% 1.36/0.54    inference(backward_demodulation,[],[f138,f438])).
% 1.36/0.54  fof(f138,plain,(
% 1.36/0.54    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl5_7),
% 1.36/0.54    inference(avatar_component_clause,[],[f136])).
% 1.36/0.54  fof(f699,plain,(
% 1.36/0.54    spl5_73 | ~spl5_5 | ~spl5_48),
% 1.36/0.54    inference(avatar_split_clause,[],[f631,f436,f127,f696])).
% 1.36/0.54  fof(f127,plain,(
% 1.36/0.54    spl5_5 <=> v1_funct_1(sK2)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.36/0.54  fof(f631,plain,(
% 1.36/0.54    v1_funct_1(k1_xboole_0) | (~spl5_5 | ~spl5_48)),
% 1.36/0.54    inference(backward_demodulation,[],[f129,f438])).
% 1.36/0.54  fof(f129,plain,(
% 1.36/0.54    v1_funct_1(sK2) | ~spl5_5),
% 1.36/0.54    inference(avatar_component_clause,[],[f127])).
% 1.36/0.54  fof(f623,plain,(
% 1.36/0.54    k1_xboole_0 != k2_relat_1(sK2) | sK1 != k2_relat_1(sK2) | k1_xboole_0 = sK1),
% 1.36/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.36/0.54  fof(f622,plain,(
% 1.36/0.54    ~spl5_3 | spl5_69),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f621])).
% 1.36/0.54  fof(f621,plain,(
% 1.36/0.54    $false | (~spl5_3 | spl5_69)),
% 1.36/0.54    inference(subsumption_resolution,[],[f119,f618])).
% 1.36/0.54  fof(f618,plain,(
% 1.36/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | spl5_69),
% 1.36/0.54    inference(resolution,[],[f615,f90])).
% 1.36/0.54  fof(f90,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f48])).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.54    inference(ennf_transformation,[],[f16])).
% 1.36/0.54  fof(f16,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.54  fof(f615,plain,(
% 1.36/0.54    ~v4_relat_1(sK2,sK0) | spl5_69),
% 1.36/0.54    inference(avatar_component_clause,[],[f613])).
% 1.36/0.54  fof(f613,plain,(
% 1.36/0.54    spl5_69 <=> v4_relat_1(sK2,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).
% 1.36/0.54  fof(f119,plain,(
% 1.36/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_3),
% 1.36/0.54    inference(avatar_component_clause,[],[f117])).
% 1.36/0.54  fof(f117,plain,(
% 1.36/0.54    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.36/0.54  fof(f616,plain,(
% 1.36/0.54    ~spl5_69 | ~spl5_15 | spl5_65),
% 1.36/0.54    inference(avatar_split_clause,[],[f610,f568,f193,f613])).
% 1.36/0.54  fof(f193,plain,(
% 1.36/0.54    spl5_15 <=> v1_relat_1(sK2)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.36/0.54  fof(f610,plain,(
% 1.36/0.54    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl5_65),
% 1.36/0.54    inference(resolution,[],[f569,f78])).
% 1.36/0.54  fof(f78,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f42])).
% 1.36/0.54  fof(f42,plain,(
% 1.36/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.36/0.54    inference(ennf_transformation,[],[f6])).
% 1.36/0.54  fof(f6,axiom,(
% 1.36/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.36/0.54  fof(f569,plain,(
% 1.36/0.54    ~r1_tarski(k1_relat_1(sK2),sK0) | spl5_65),
% 1.36/0.54    inference(avatar_component_clause,[],[f568])).
% 1.36/0.54  fof(f605,plain,(
% 1.36/0.54    ~spl5_41 | ~spl5_65 | spl5_23 | ~spl5_40 | ~spl5_61),
% 1.36/0.54    inference(avatar_split_clause,[],[f602,f544,f389,f246,f568,f394])).
% 1.36/0.54  fof(f394,plain,(
% 1.36/0.54    spl5_41 <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.36/0.54  fof(f389,plain,(
% 1.36/0.54    spl5_40 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 1.36/0.54  fof(f544,plain,(
% 1.36/0.54    spl5_61 <=> ! [X0] : (~v1_funct_2(k2_funct_1(sK2),sK1,X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 1.36/0.54  fof(f602,plain,(
% 1.36/0.54    k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl5_40 | ~spl5_61)),
% 1.36/0.54    inference(resolution,[],[f545,f391])).
% 1.36/0.54  fof(f391,plain,(
% 1.36/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl5_40),
% 1.36/0.54    inference(avatar_component_clause,[],[f389])).
% 1.36/0.54  fof(f545,plain,(
% 1.36/0.54    ( ! [X0] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK1,X0)) ) | ~spl5_61),
% 1.36/0.54    inference(avatar_component_clause,[],[f544])).
% 1.36/0.54  fof(f558,plain,(
% 1.36/0.54    ~spl5_8 | spl5_61 | spl5_7),
% 1.36/0.54    inference(avatar_split_clause,[],[f556,f136,f544,f140])).
% 1.36/0.54  fof(f140,plain,(
% 1.36/0.54    spl5_8 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.36/0.54  fof(f556,plain,(
% 1.36/0.54    ( ! [X0] : (~v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(X0,sK0) | k1_xboole_0 = X0 | ~v1_funct_1(k2_funct_1(sK2))) ) | spl5_7),
% 1.36/0.54    inference(resolution,[],[f138,f95])).
% 1.36/0.55  fof(f95,plain,(
% 1.36/0.55    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f52])).
% 1.36/0.55  fof(f546,plain,(
% 1.36/0.55    ~spl5_8 | spl5_61 | spl5_6),
% 1.36/0.55    inference(avatar_split_clause,[],[f536,f132,f544,f140])).
% 1.36/0.55  fof(f536,plain,(
% 1.36/0.55    ( ! [X0] : (~v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(X0,sK0) | k1_xboole_0 = X0 | ~v1_funct_1(k2_funct_1(sK2))) ) | spl5_6),
% 1.36/0.55    inference(resolution,[],[f96,f134])).
% 1.36/0.55  fof(f96,plain,(
% 1.36/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f52])).
% 1.36/0.55  fof(f439,plain,(
% 1.36/0.55    spl5_48 | ~spl5_15 | ~spl5_44 | ~spl5_39),
% 1.36/0.55    inference(avatar_split_clause,[],[f414,f379,f416,f193,f436])).
% 1.36/0.55  fof(f379,plain,(
% 1.36/0.55    spl5_39 <=> sK1 = k2_relat_1(sK2)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.36/0.55  fof(f414,plain,(
% 1.36/0.55    k1_xboole_0 != sK1 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl5_39),
% 1.36/0.55    inference(superposition,[],[f61,f381])).
% 1.36/0.55  fof(f381,plain,(
% 1.36/0.55    sK1 = k2_relat_1(sK2) | ~spl5_39),
% 1.36/0.55    inference(avatar_component_clause,[],[f379])).
% 1.36/0.55  fof(f61,plain,(
% 1.36/0.55    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f32])).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f31])).
% 1.36/0.55  fof(f31,plain,(
% 1.36/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f9])).
% 1.36/0.55  fof(f9,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.36/0.55  fof(f429,plain,(
% 1.36/0.55    ~spl5_15 | ~spl5_5 | spl5_46 | ~spl5_39),
% 1.36/0.55    inference(avatar_split_clause,[],[f411,f379,f426,f127,f193])).
% 1.36/0.55  fof(f411,plain,(
% 1.36/0.55    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl5_39),
% 1.36/0.55    inference(superposition,[],[f64,f381])).
% 1.36/0.55  fof(f64,plain,(
% 1.36/0.55    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f35])).
% 1.36/0.55  fof(f35,plain,(
% 1.36/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f34])).
% 1.36/0.55  fof(f34,plain,(
% 1.36/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f20])).
% 1.36/0.55  fof(f20,axiom,(
% 1.36/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.36/0.55  fof(f397,plain,(
% 1.36/0.55    spl5_41 | ~spl5_21 | ~spl5_39),
% 1.36/0.55    inference(avatar_split_clause,[],[f385,f379,f236,f394])).
% 1.36/0.55  fof(f236,plain,(
% 1.36/0.55    spl5_21 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.36/0.55  fof(f385,plain,(
% 1.36/0.55    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl5_21 | ~spl5_39)),
% 1.36/0.55    inference(backward_demodulation,[],[f238,f381])).
% 1.36/0.55  fof(f238,plain,(
% 1.36/0.55    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl5_21),
% 1.36/0.55    inference(avatar_component_clause,[],[f236])).
% 1.36/0.55  fof(f392,plain,(
% 1.36/0.55    spl5_40 | ~spl5_20 | ~spl5_39),
% 1.36/0.55    inference(avatar_split_clause,[],[f384,f379,f230,f389])).
% 1.36/0.55  fof(f230,plain,(
% 1.36/0.55    spl5_20 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.36/0.55  fof(f384,plain,(
% 1.36/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl5_20 | ~spl5_39)),
% 1.36/0.55    inference(backward_demodulation,[],[f232,f381])).
% 1.36/0.55  fof(f232,plain,(
% 1.36/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl5_20),
% 1.36/0.55    inference(avatar_component_clause,[],[f230])).
% 1.36/0.55  fof(f382,plain,(
% 1.36/0.55    spl5_39 | ~spl5_1 | ~spl5_3),
% 1.36/0.55    inference(avatar_split_clause,[],[f377,f117,f107,f379])).
% 1.36/0.55  fof(f107,plain,(
% 1.36/0.55    spl5_1 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.36/0.55  fof(f377,plain,(
% 1.36/0.55    sK1 = k2_relat_1(sK2) | (~spl5_1 | ~spl5_3)),
% 1.36/0.55    inference(forward_demodulation,[],[f367,f109])).
% 1.36/0.55  fof(f109,plain,(
% 1.36/0.55    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl5_1),
% 1.36/0.55    inference(avatar_component_clause,[],[f107])).
% 1.36/0.55  fof(f367,plain,(
% 1.36/0.55    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl5_3),
% 1.36/0.55    inference(resolution,[],[f89,f119])).
% 1.36/0.55  fof(f89,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f47])).
% 1.36/0.55  fof(f47,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f17])).
% 1.36/0.55  fof(f17,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.36/0.55  fof(f282,plain,(
% 1.36/0.55    spl5_25 | ~spl5_19 | ~spl5_23 | ~spl5_17),
% 1.36/0.55    inference(avatar_split_clause,[],[f273,f210,f246,f226,f255])).
% 1.36/0.55  fof(f226,plain,(
% 1.36/0.55    spl5_19 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.36/0.55  fof(f210,plain,(
% 1.36/0.55    spl5_17 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.36/0.55  fof(f273,plain,(
% 1.36/0.55    k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_funct_1(sK2) | ~spl5_17),
% 1.36/0.55    inference(superposition,[],[f61,f212])).
% 1.36/0.55  fof(f212,plain,(
% 1.36/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl5_17),
% 1.36/0.55    inference(avatar_component_clause,[],[f210])).
% 1.36/0.55  fof(f277,plain,(
% 1.36/0.55    ~spl5_19 | ~spl5_23 | spl5_22 | ~spl5_14 | ~spl5_17),
% 1.36/0.55    inference(avatar_split_clause,[],[f276,f210,f189,f242,f246,f226])).
% 1.36/0.55  fof(f242,plain,(
% 1.36/0.55    spl5_22 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.36/0.55  fof(f189,plain,(
% 1.36/0.55    spl5_14 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.36/0.55  fof(f276,plain,(
% 1.36/0.55    k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_14 | ~spl5_17)),
% 1.36/0.55    inference(forward_demodulation,[],[f271,f191])).
% 1.36/0.55  fof(f191,plain,(
% 1.36/0.55    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl5_14),
% 1.36/0.55    inference(avatar_component_clause,[],[f189])).
% 1.36/0.55  fof(f271,plain,(
% 1.36/0.55    k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~spl5_17),
% 1.36/0.55    inference(superposition,[],[f62,f212])).
% 1.36/0.55  fof(f62,plain,(
% 1.36/0.55    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f33])).
% 1.36/0.55  fof(f33,plain,(
% 1.36/0.55    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f10])).
% 1.36/0.55  fof(f10,axiom,(
% 1.36/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.36/0.55  fof(f268,plain,(
% 1.36/0.55    ~spl5_15 | ~spl5_5 | spl5_8),
% 1.36/0.55    inference(avatar_split_clause,[],[f265,f140,f127,f193])).
% 1.36/0.55  fof(f265,plain,(
% 1.36/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_8),
% 1.36/0.55    inference(resolution,[],[f142,f67])).
% 1.36/0.55  fof(f67,plain,(
% 1.36/0.55    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f37])).
% 1.36/0.55  fof(f37,plain,(
% 1.36/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f36])).
% 1.36/0.55  fof(f36,plain,(
% 1.36/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f12])).
% 1.36/0.55  fof(f12,axiom,(
% 1.36/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.36/0.55  fof(f142,plain,(
% 1.36/0.55    ~v1_funct_1(k2_funct_1(sK2)) | spl5_8),
% 1.36/0.55    inference(avatar_component_clause,[],[f140])).
% 1.36/0.55  fof(f263,plain,(
% 1.36/0.55    ~spl5_15 | ~spl5_5 | spl5_19),
% 1.36/0.55    inference(avatar_split_clause,[],[f260,f226,f127,f193])).
% 1.36/0.55  fof(f260,plain,(
% 1.36/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl5_19),
% 1.36/0.55    inference(resolution,[],[f228,f66])).
% 1.36/0.55  fof(f66,plain,(
% 1.36/0.55    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f37])).
% 1.36/0.55  fof(f228,plain,(
% 1.36/0.55    ~v1_relat_1(k2_funct_1(sK2)) | spl5_19),
% 1.36/0.55    inference(avatar_component_clause,[],[f226])).
% 1.36/0.55  fof(f239,plain,(
% 1.36/0.55    ~spl5_19 | ~spl5_8 | spl5_21 | ~spl5_14 | ~spl5_17),
% 1.36/0.55    inference(avatar_split_clause,[],[f234,f210,f189,f236,f140,f226])).
% 1.36/0.55  fof(f234,plain,(
% 1.36/0.55    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_14 | ~spl5_17)),
% 1.36/0.55    inference(forward_demodulation,[],[f220,f212])).
% 1.36/0.55  fof(f220,plain,(
% 1.36/0.55    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl5_14),
% 1.36/0.55    inference(superposition,[],[f64,f191])).
% 1.36/0.55  fof(f233,plain,(
% 1.36/0.55    ~spl5_19 | ~spl5_8 | spl5_20 | ~spl5_14 | ~spl5_17),
% 1.36/0.55    inference(avatar_split_clause,[],[f224,f210,f189,f230,f140,f226])).
% 1.36/0.55  fof(f224,plain,(
% 1.36/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_14 | ~spl5_17)),
% 1.36/0.55    inference(forward_demodulation,[],[f219,f212])).
% 1.36/0.55  fof(f219,plain,(
% 1.36/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl5_14),
% 1.36/0.55    inference(superposition,[],[f65,f191])).
% 1.36/0.55  fof(f65,plain,(
% 1.36/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f35])).
% 1.36/0.55  fof(f213,plain,(
% 1.36/0.55    spl5_17 | ~spl5_15 | ~spl5_5 | ~spl5_2),
% 1.36/0.55    inference(avatar_split_clause,[],[f207,f112,f127,f193,f210])).
% 1.36/0.55  fof(f112,plain,(
% 1.36/0.55    spl5_2 <=> v2_funct_1(sK2)),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.36/0.55  fof(f207,plain,(
% 1.36/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl5_2),
% 1.36/0.55    inference(resolution,[],[f69,f114])).
% 1.36/0.55  fof(f114,plain,(
% 1.36/0.55    v2_funct_1(sK2) | ~spl5_2),
% 1.36/0.55    inference(avatar_component_clause,[],[f112])).
% 1.36/0.55  fof(f69,plain,(
% 1.36/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f39])).
% 1.36/0.55  fof(f39,plain,(
% 1.36/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.55    inference(flattening,[],[f38])).
% 1.36/0.55  fof(f38,plain,(
% 1.36/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f14])).
% 1.36/0.55  fof(f14,axiom,(
% 1.36/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.36/0.55  fof(f206,plain,(
% 1.36/0.55    ~spl5_3 | spl5_15),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f205])).
% 1.36/0.55  fof(f205,plain,(
% 1.36/0.55    $false | (~spl5_3 | spl5_15)),
% 1.36/0.55    inference(subsumption_resolution,[],[f119,f203])).
% 1.36/0.55  fof(f203,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_15),
% 1.36/0.55    inference(resolution,[],[f195,f88])).
% 1.36/0.55  fof(f88,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f46])).
% 1.36/0.55  fof(f46,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.55    inference(ennf_transformation,[],[f15])).
% 1.36/0.55  fof(f15,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.36/0.55  fof(f195,plain,(
% 1.36/0.55    ~v1_relat_1(sK2) | spl5_15),
% 1.36/0.55    inference(avatar_component_clause,[],[f193])).
% 1.36/0.55  fof(f196,plain,(
% 1.36/0.55    spl5_14 | ~spl5_15 | ~spl5_5 | ~spl5_2),
% 1.36/0.55    inference(avatar_split_clause,[],[f186,f112,f127,f193,f189])).
% 1.36/0.55  fof(f186,plain,(
% 1.36/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl5_2),
% 1.36/0.55    inference(resolution,[],[f68,f114])).
% 1.36/0.55  fof(f68,plain,(
% 1.36/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f39])).
% 1.36/0.55  fof(f143,plain,(
% 1.36/0.55    ~spl5_6 | ~spl5_7 | ~spl5_8),
% 1.36/0.55    inference(avatar_split_clause,[],[f53,f140,f136,f132])).
% 1.36/0.55  fof(f53,plain,(
% 1.36/0.55    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  fof(f30,plain,(
% 1.36/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.36/0.55    inference(flattening,[],[f29])).
% 1.36/0.55  fof(f29,plain,(
% 1.36/0.55    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.36/0.55    inference(ennf_transformation,[],[f23])).
% 1.36/0.55  fof(f23,negated_conjecture,(
% 1.36/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.36/0.55    inference(negated_conjecture,[],[f22])).
% 1.36/0.55  fof(f22,conjecture,(
% 1.36/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.36/0.55  fof(f130,plain,(
% 1.36/0.55    spl5_5),
% 1.36/0.55    inference(avatar_split_clause,[],[f54,f127])).
% 1.36/0.55  fof(f54,plain,(
% 1.36/0.55    v1_funct_1(sK2)),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  fof(f120,plain,(
% 1.36/0.55    spl5_3),
% 1.36/0.55    inference(avatar_split_clause,[],[f56,f117])).
% 1.36/0.55  fof(f56,plain,(
% 1.36/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  fof(f115,plain,(
% 1.36/0.55    spl5_2),
% 1.36/0.55    inference(avatar_split_clause,[],[f57,f112])).
% 1.36/0.55  fof(f57,plain,(
% 1.36/0.55    v2_funct_1(sK2)),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  fof(f110,plain,(
% 1.36/0.55    spl5_1),
% 1.36/0.55    inference(avatar_split_clause,[],[f58,f107])).
% 1.36/0.55  fof(f58,plain,(
% 1.36/0.55    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.36/0.55    inference(cnf_transformation,[],[f30])).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (9124)------------------------------
% 1.36/0.55  % (9124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (9124)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (9124)Memory used [KB]: 6908
% 1.36/0.55  % (9124)Time elapsed: 0.083 s
% 1.36/0.55  % (9124)------------------------------
% 1.36/0.55  % (9124)------------------------------
% 1.36/0.55  % (9128)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.48/0.55  % (9108)Success in time 0.19 s
%------------------------------------------------------------------------------
