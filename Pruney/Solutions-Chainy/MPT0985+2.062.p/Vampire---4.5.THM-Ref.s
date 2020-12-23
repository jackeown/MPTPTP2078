%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 438 expanded)
%              Number of leaves         :   56 ( 200 expanded)
%              Depth                    :    9
%              Number of atoms          :  679 (1302 expanded)
%              Number of equality atoms :  108 ( 253 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1671,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f132,f145,f150,f237,f290,f301,f344,f349,f436,f441,f460,f464,f542,f562,f567,f576,f581,f603,f657,f662,f699,f880,f891,f1048,f1059,f1065,f1067,f1068,f1084,f1086,f1206,f1474,f1567,f1639,f1655,f1670])).

fof(f1670,plain,
    ( ~ spl3_20
    | spl3_6
    | ~ spl3_72
    | ~ spl3_76
    | ~ spl3_149 ),
    inference(avatar_split_clause,[],[f1669,f1471,f696,f676,f134,f292])).

fof(f292,plain,
    ( spl3_20
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f134,plain,
    ( spl3_6
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f676,plain,
    ( spl3_72
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f696,plain,
    ( spl3_76
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f1471,plain,
    ( spl3_149
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_149])])).

fof(f1669,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_6
    | ~ spl3_72
    | ~ spl3_76
    | ~ spl3_149 ),
    inference(forward_demodulation,[],[f1668,f1473])).

fof(f1473,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_149 ),
    inference(avatar_component_clause,[],[f1471])).

fof(f1668,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl3_6
    | ~ spl3_72
    | ~ spl3_76 ),
    inference(forward_demodulation,[],[f1667,f698])).

fof(f698,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f696])).

fof(f1667,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl3_6
    | ~ spl3_72 ),
    inference(forward_demodulation,[],[f1666,f105])).

fof(f105,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1666,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_6
    | ~ spl3_72 ),
    inference(forward_demodulation,[],[f136,f677])).

fof(f677,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f676])).

fof(f136,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f1655,plain,
    ( ~ spl3_114
    | ~ spl3_15
    | ~ spl3_156 ),
    inference(avatar_split_clause,[],[f1651,f1637,f217,f1081])).

fof(f1081,plain,
    ( spl3_114
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).

fof(f217,plain,
    ( spl3_15
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f1637,plain,
    ( spl3_156
  <=> ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_156])])).

fof(f1651,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_15
    | ~ spl3_156 ),
    inference(resolution,[],[f1638,f242])).

fof(f242,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f154,f218])).

fof(f218,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f217])).

fof(f154,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(superposition,[],[f78,f104])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(f1638,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl3_156 ),
    inference(avatar_component_clause,[],[f1637])).

fof(f1639,plain,
    ( ~ spl3_20
    | spl3_156
    | ~ spl3_19
    | spl3_153 ),
    inference(avatar_split_clause,[],[f1634,f1564,f266,f1637,f292])).

fof(f266,plain,
    ( spl3_19
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f1564,plain,
    ( spl3_153
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_153])])).

fof(f1634,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ r1_tarski(X0,sK0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) )
    | spl3_153 ),
    inference(resolution,[],[f1566,f153])).

fof(f153,plain,(
    ! [X2,X3,X1] :
      ( v1_funct_2(X3,k1_xboole_0,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f107,f105])).

fof(f107,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ r1_tarski(X1,X2)
      | v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 != X0
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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

fof(f1566,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_153 ),
    inference(avatar_component_clause,[],[f1564])).

fof(f1567,plain,
    ( ~ spl3_153
    | ~ spl3_72
    | spl3_121
    | ~ spl3_149 ),
    inference(avatar_split_clause,[],[f1562,f1471,f1203,f676,f1564])).

fof(f1203,plain,
    ( spl3_121
  <=> v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_121])])).

fof(f1562,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl3_72
    | spl3_121
    | ~ spl3_149 ),
    inference(forward_demodulation,[],[f1561,f1473])).

fof(f1561,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ spl3_72
    | spl3_121 ),
    inference(forward_demodulation,[],[f1205,f677])).

fof(f1205,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0)
    | spl3_121 ),
    inference(avatar_component_clause,[],[f1203])).

fof(f1474,plain,
    ( spl3_149
    | ~ spl3_43
    | ~ spl3_76 ),
    inference(avatar_split_clause,[],[f1469,f696,f452,f1471])).

fof(f452,plain,
    ( spl3_43
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f1469,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_43
    | ~ spl3_76 ),
    inference(forward_demodulation,[],[f454,f698])).

fof(f454,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f452])).

fof(f1206,plain,
    ( ~ spl3_121
    | spl3_7
    | ~ spl3_76 ),
    inference(avatar_split_clause,[],[f1112,f696,f138,f1203])).

fof(f138,plain,
    ( spl3_7
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1112,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0)
    | spl3_7
    | ~ spl3_76 ),
    inference(backward_demodulation,[],[f140,f698])).

fof(f140,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f1086,plain,
    ( ~ spl3_17
    | ~ spl3_19
    | spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f1085,f298,f292,f266,f258])).

fof(f258,plain,
    ( spl3_17
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f298,plain,
    ( spl3_21
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f1085,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f323,f104])).

fof(f323,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_21 ),
    inference(superposition,[],[f72,f300])).

fof(f300,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f298])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f1084,plain,
    ( ~ spl3_17
    | ~ spl3_19
    | spl3_114
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f1079,f298,f217,f1081,f266,f258])).

% (23829)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f1079,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_15
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f324,f218])).

fof(f324,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_21 ),
    inference(superposition,[],[f71,f300])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1068,plain,
    ( k1_xboole_0 != k2_funct_1(sK2)
    | v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1067,plain,
    ( sK1 != k2_relat_1(sK2)
    | k1_xboole_0 != k2_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1065,plain,
    ( ~ spl3_3
    | spl3_113 ),
    inference(avatar_contradiction_clause,[],[f1064])).

fof(f1064,plain,
    ( $false
    | ~ spl3_3
    | spl3_113 ),
    inference(subsumption_resolution,[],[f121,f1061])).

fof(f1061,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | spl3_113 ),
    inference(resolution,[],[f1058,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1058,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl3_113 ),
    inference(avatar_component_clause,[],[f1056])).

fof(f1056,plain,
    ( spl3_113
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).

fof(f121,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1059,plain,
    ( ~ spl3_113
    | ~ spl3_25
    | spl3_96 ),
    inference(avatar_split_clause,[],[f1054,f899,f341,f1056])).

fof(f341,plain,
    ( spl3_25
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f899,plain,
    ( spl3_96
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f1054,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl3_96 ),
    inference(resolution,[],[f900,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f900,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_96 ),
    inference(avatar_component_clause,[],[f899])).

fof(f1048,plain,
    ( ~ spl3_70
    | ~ spl3_96
    | spl3_27
    | ~ spl3_69
    | ~ spl3_93 ),
    inference(avatar_split_clause,[],[f1044,f878,f654,f360,f899,f659])).

fof(f659,plain,
    ( spl3_70
  <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f360,plain,
    ( spl3_27
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f654,plain,
    ( spl3_69
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f878,plain,
    ( spl3_93
  <=> ! [X8] :
        ( ~ v1_funct_2(k2_funct_1(sK2),sK1,X8)
        | k1_xboole_0 = X8
        | ~ r1_tarski(X8,sK0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f1044,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl3_69
    | ~ spl3_93 ),
    inference(resolution,[],[f879,f656])).

fof(f656,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f654])).

fof(f879,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X8)))
        | k1_xboole_0 = X8
        | ~ r1_tarski(X8,sK0)
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,X8) )
    | ~ spl3_93 ),
    inference(avatar_component_clause,[],[f878])).

fof(f891,plain,
    ( ~ spl3_8
    | spl3_93
    | spl3_7 ),
    inference(avatar_split_clause,[],[f890,f138,f878,f142])).

fof(f142,plain,
    ( spl3_8
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f890,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | spl3_7 ),
    inference(resolution,[],[f140,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f880,plain,
    ( ~ spl3_8
    | spl3_93
    | spl3_6 ),
    inference(avatar_split_clause,[],[f871,f134,f878,f142])).

fof(f871,plain,
    ( ! [X8] :
        ( ~ v1_funct_2(k2_funct_1(sK2),sK1,X8)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X8)))
        | ~ r1_tarski(X8,sK0)
        | k1_xboole_0 = X8
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | spl3_6 ),
    inference(resolution,[],[f101,f136])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X1,X2)
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f699,plain,
    ( spl3_76
    | ~ spl3_25
    | ~ spl3_72
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f674,f600,f676,f341,f696])).

fof(f600,plain,
    ( spl3_61
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f674,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_61 ),
    inference(superposition,[],[f66,f602])).

fof(f602,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f600])).

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f662,plain,
    ( spl3_70
    | ~ spl3_58
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f614,f600,f564,f659])).

fof(f564,plain,
    ( spl3_58
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f614,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl3_58
    | ~ spl3_61 ),
    inference(backward_demodulation,[],[f566,f602])).

fof(f566,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f564])).

fof(f657,plain,
    ( spl3_69
    | ~ spl3_57
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f613,f600,f559,f654])).

fof(f559,plain,
    ( spl3_57
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f613,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_57
    | ~ spl3_61 ),
    inference(backward_demodulation,[],[f561,f602])).

fof(f561,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f559])).

fof(f603,plain,
    ( spl3_61
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f598,f119,f109,f600])).

fof(f109,plain,
    ( spl3_1
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f598,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f595,f111])).

fof(f111,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f595,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f94,f121])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f581,plain,
    ( spl3_43
    | ~ spl3_38
    | ~ spl3_27
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f572,f539,f360,f429,f452])).

fof(f429,plain,
    ( spl3_38
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f539,plain,
    ( spl3_54
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f572,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_54 ),
    inference(superposition,[],[f66,f541])).

fof(f541,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f539])).

fof(f576,plain,
    ( ~ spl3_38
    | ~ spl3_27
    | spl3_29
    | ~ spl3_24
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f575,f539,f337,f369,f360,f429])).

fof(f369,plain,
    ( spl3_29
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f337,plain,
    ( spl3_24
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

% (23841)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f575,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_24
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f570,f339])).

fof(f339,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f337])).

fof(f570,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_54 ),
    inference(superposition,[],[f67,f541])).

fof(f67,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f567,plain,
    ( spl3_58
    | ~ spl3_40
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f547,f539,f438,f564])).

fof(f438,plain,
    ( spl3_40
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f547,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_40
    | ~ spl3_54 ),
    inference(backward_demodulation,[],[f440,f541])).

fof(f440,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f438])).

fof(f562,plain,
    ( spl3_57
    | ~ spl3_39
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f546,f539,f433,f559])).

fof(f433,plain,
    ( spl3_39
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f546,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_39
    | ~ spl3_54 ),
    inference(backward_demodulation,[],[f435,f541])).

fof(f435,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f433])).

fof(f542,plain,
    ( spl3_54
    | ~ spl3_25
    | ~ spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f537,f114,f129,f341,f539])).

fof(f129,plain,
    ( spl3_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f114,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f537,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f76,f116])).

fof(f116,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f464,plain,
    ( ~ spl3_25
    | ~ spl3_5
    | spl3_8 ),
    inference(avatar_split_clause,[],[f462,f142,f129,f341])).

fof(f462,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_8 ),
    inference(resolution,[],[f144,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f144,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f460,plain,
    ( ~ spl3_25
    | ~ spl3_5
    | spl3_38 ),
    inference(avatar_split_clause,[],[f457,f429,f129,f341])).

fof(f457,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_38 ),
    inference(resolution,[],[f431,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f431,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f429])).

fof(f441,plain,
    ( ~ spl3_38
    | ~ spl3_8
    | spl3_40
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f424,f337,f438,f142,f429])).

fof(f424,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_24 ),
    inference(superposition,[],[f71,f339])).

fof(f436,plain,
    ( ~ spl3_38
    | ~ spl3_8
    | spl3_39
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f423,f337,f433,f142,f429])).

fof(f423,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_24 ),
    inference(superposition,[],[f72,f339])).

fof(f349,plain,
    ( ~ spl3_3
    | spl3_25 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | ~ spl3_3
    | spl3_25 ),
    inference(subsumption_resolution,[],[f121,f346])).

fof(f346,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_25 ),
    inference(resolution,[],[f343,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f343,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_25 ),
    inference(avatar_component_clause,[],[f341])).

fof(f344,plain,
    ( spl3_24
    | ~ spl3_25
    | ~ spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f335,f114,f129,f341,f337])).

fof(f335,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f75,f116])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f301,plain,
    ( ~ spl3_17
    | spl3_21
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f285,f217,f298,f258])).

fof(f285,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_15 ),
    inference(trivial_inequality_removal,[],[f282])).

% (23826)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f282,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_15 ),
    inference(superposition,[],[f68,f218])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f290,plain,
    ( ~ spl3_15
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl3_15
    | spl3_17 ),
    inference(unit_resulting_resolution,[],[f242,f277,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

% (23840)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f277,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_17 ),
    inference(resolution,[],[f260,f93])).

fof(f260,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f258])).

fof(f237,plain,
    ( spl3_15
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f231,f147,f217])).

fof(f147,plain,
    ( spl3_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f231,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_9 ),
    inference(resolution,[],[f225,f154])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_9 ),
    inference(resolution,[],[f223,f87])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl3_9 ),
    inference(resolution,[],[f174,f149])).

fof(f149,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k1_xboole_0 = X0 )
    | ~ spl3_9 ),
    inference(resolution,[],[f69,f170])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_9 ),
    inference(resolution,[],[f92,f149])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f150,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f62,f147])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f145,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f56,f142,f138,f134])).

fof(f56,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
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

fof(f132,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f57,f129])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f122,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f59,f119])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f117,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f60,f114])).

fof(f60,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f112,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f61,f109])).

fof(f61,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (23828)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.47  % (23828)Refutation not found, incomplete strategy% (23828)------------------------------
% 0.21/0.47  % (23828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23837)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (23828)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (23828)Memory used [KB]: 10746
% 0.21/0.49  % (23828)Time elapsed: 0.056 s
% 0.21/0.49  % (23828)------------------------------
% 0.21/0.49  % (23828)------------------------------
% 0.21/0.49  % (23823)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (23844)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (23824)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (23846)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.50  % (23822)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (23845)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (23837)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f1671,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f112,f117,f122,f132,f145,f150,f237,f290,f301,f344,f349,f436,f441,f460,f464,f542,f562,f567,f576,f581,f603,f657,f662,f699,f880,f891,f1048,f1059,f1065,f1067,f1068,f1084,f1086,f1206,f1474,f1567,f1639,f1655,f1670])).
% 0.21/0.51  fof(f1670,plain,(
% 0.21/0.51    ~spl3_20 | spl3_6 | ~spl3_72 | ~spl3_76 | ~spl3_149),
% 0.21/0.51    inference(avatar_split_clause,[],[f1669,f1471,f696,f676,f134,f292])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    spl3_20 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl3_6 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f676,plain,(
% 0.21/0.51    spl3_72 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.21/0.51  fof(f696,plain,(
% 0.21/0.51    spl3_76 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 0.21/0.51  fof(f1471,plain,(
% 0.21/0.51    spl3_149 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_149])])).
% 0.21/0.51  fof(f1669,plain,(
% 0.21/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl3_6 | ~spl3_72 | ~spl3_76 | ~spl3_149)),
% 0.21/0.51    inference(forward_demodulation,[],[f1668,f1473])).
% 0.21/0.51  fof(f1473,plain,(
% 0.21/0.51    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl3_149),
% 0.21/0.51    inference(avatar_component_clause,[],[f1471])).
% 0.21/0.51  fof(f1668,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl3_6 | ~spl3_72 | ~spl3_76)),
% 0.21/0.51    inference(forward_demodulation,[],[f1667,f698])).
% 0.21/0.51  fof(f698,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | ~spl3_76),
% 0.21/0.51    inference(avatar_component_clause,[],[f696])).
% 0.21/0.51  fof(f1667,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl3_6 | ~spl3_72)),
% 0.21/0.51    inference(forward_demodulation,[],[f1666,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f1666,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_6 | ~spl3_72)),
% 0.21/0.51    inference(forward_demodulation,[],[f136,f677])).
% 0.21/0.51  fof(f677,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl3_72),
% 0.21/0.51    inference(avatar_component_clause,[],[f676])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f134])).
% 0.21/0.51  fof(f1655,plain,(
% 0.21/0.51    ~spl3_114 | ~spl3_15 | ~spl3_156),
% 0.21/0.51    inference(avatar_split_clause,[],[f1651,f1637,f217,f1081])).
% 0.21/0.51  fof(f1081,plain,(
% 0.21/0.51    spl3_114 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    spl3_15 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.51  fof(f1637,plain,(
% 0.21/0.51    spl3_156 <=> ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(X0,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_156])])).
% 0.21/0.51  fof(f1651,plain,(
% 0.21/0.51    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_15 | ~spl3_156)),
% 0.21/0.51    inference(resolution,[],[f1638,f242])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_15),
% 0.21/0.51    inference(backward_demodulation,[],[f154,f218])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f217])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.21/0.51    inference(superposition,[],[f78,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).
% 0.21/0.51  fof(f1638,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl3_156),
% 0.21/0.51    inference(avatar_component_clause,[],[f1637])).
% 0.21/0.51  fof(f1639,plain,(
% 0.21/0.51    ~spl3_20 | spl3_156 | ~spl3_19 | spl3_153),
% 0.21/0.51    inference(avatar_split_clause,[],[f1634,f1564,f266,f1637,f292])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    spl3_19 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.51  fof(f1564,plain,(
% 0.21/0.51    spl3_153 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_153])])).
% 0.21/0.51  fof(f1634,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(X0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))) ) | spl3_153),
% 0.21/0.51    inference(resolution,[],[f1566,f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (v1_funct_2(X3,k1_xboole_0,X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f107,f105])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_tarski(X1,X2) | v1_funct_2(X3,k1_xboole_0,X2)) )),
% 0.21/0.51    inference(equality_resolution,[],[f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 != X0 | v1_funct_2(X3,X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 0.21/0.51  fof(f1566,plain,(
% 0.21/0.51    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | spl3_153),
% 0.21/0.51    inference(avatar_component_clause,[],[f1564])).
% 0.21/0.51  fof(f1567,plain,(
% 0.21/0.51    ~spl3_153 | ~spl3_72 | spl3_121 | ~spl3_149),
% 0.21/0.51    inference(avatar_split_clause,[],[f1562,f1471,f1203,f676,f1564])).
% 0.21/0.51  fof(f1203,plain,(
% 0.21/0.51    spl3_121 <=> v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_121])])).
% 0.21/0.51  fof(f1562,plain,(
% 0.21/0.51    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (~spl3_72 | spl3_121 | ~spl3_149)),
% 0.21/0.51    inference(forward_demodulation,[],[f1561,f1473])).
% 0.21/0.51  fof(f1561,plain,(
% 0.21/0.51    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (~spl3_72 | spl3_121)),
% 0.21/0.51    inference(forward_demodulation,[],[f1205,f677])).
% 0.21/0.51  fof(f1205,plain,(
% 0.21/0.51    ~v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0) | spl3_121),
% 0.21/0.51    inference(avatar_component_clause,[],[f1203])).
% 0.21/0.51  fof(f1474,plain,(
% 0.21/0.51    spl3_149 | ~spl3_43 | ~spl3_76),
% 0.21/0.51    inference(avatar_split_clause,[],[f1469,f696,f452,f1471])).
% 0.21/0.51  fof(f452,plain,(
% 0.21/0.51    spl3_43 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.51  fof(f1469,plain,(
% 0.21/0.51    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_43 | ~spl3_76)),
% 0.21/0.51    inference(forward_demodulation,[],[f454,f698])).
% 0.21/0.51  fof(f454,plain,(
% 0.21/0.51    k1_xboole_0 = k2_funct_1(sK2) | ~spl3_43),
% 0.21/0.51    inference(avatar_component_clause,[],[f452])).
% 0.21/0.51  fof(f1206,plain,(
% 0.21/0.51    ~spl3_121 | spl3_7 | ~spl3_76),
% 0.21/0.51    inference(avatar_split_clause,[],[f1112,f696,f138,f1203])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    spl3_7 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f1112,plain,(
% 0.21/0.51    ~v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0) | (spl3_7 | ~spl3_76)),
% 0.21/0.51    inference(backward_demodulation,[],[f140,f698])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f138])).
% 0.21/0.51  fof(f1086,plain,(
% 0.21/0.51    ~spl3_17 | ~spl3_19 | spl3_20 | ~spl3_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f1085,f298,f292,f266,f258])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    spl3_17 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    spl3_21 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.51  fof(f1085,plain,(
% 0.21/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl3_21),
% 0.21/0.51    inference(forward_demodulation,[],[f323,f104])).
% 0.21/0.51  fof(f323,plain,(
% 0.21/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl3_21),
% 0.21/0.51    inference(superposition,[],[f72,f300])).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f298])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.51  fof(f1084,plain,(
% 0.21/0.51    ~spl3_17 | ~spl3_19 | spl3_114 | ~spl3_15 | ~spl3_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f1079,f298,f217,f1081,f266,f258])).
% 0.21/0.51  % (23829)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  fof(f1079,plain,(
% 0.21/0.51    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl3_15 | ~spl3_21)),
% 0.21/0.51    inference(forward_demodulation,[],[f324,f218])).
% 0.21/0.51  fof(f324,plain,(
% 0.21/0.51    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl3_21),
% 0.21/0.51    inference(superposition,[],[f71,f300])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f1068,plain,(
% 0.21/0.51    k1_xboole_0 != k2_funct_1(sK2) | v1_funct_1(k1_xboole_0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f1067,plain,(
% 0.21/0.51    sK1 != k2_relat_1(sK2) | k1_xboole_0 != k2_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f1065,plain,(
% 0.21/0.51    ~spl3_3 | spl3_113),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1064])).
% 0.21/0.51  fof(f1064,plain,(
% 0.21/0.51    $false | (~spl3_3 | spl3_113)),
% 0.21/0.51    inference(subsumption_resolution,[],[f121,f1061])).
% 0.21/0.51  fof(f1061,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | spl3_113),
% 0.21/0.51    inference(resolution,[],[f1058,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f1058,plain,(
% 0.21/0.51    ~v4_relat_1(sK2,sK0) | spl3_113),
% 0.21/0.51    inference(avatar_component_clause,[],[f1056])).
% 0.21/0.51  fof(f1056,plain,(
% 0.21/0.51    spl3_113 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_113])])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f1059,plain,(
% 0.21/0.51    ~spl3_113 | ~spl3_25 | spl3_96),
% 0.21/0.51    inference(avatar_split_clause,[],[f1054,f899,f341,f1056])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    spl3_25 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.51  fof(f899,plain,(
% 0.21/0.51    spl3_96 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 0.21/0.51  fof(f1054,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl3_96),
% 0.21/0.51    inference(resolution,[],[f900,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.51  fof(f900,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_96),
% 0.21/0.51    inference(avatar_component_clause,[],[f899])).
% 0.21/0.51  fof(f1048,plain,(
% 0.21/0.51    ~spl3_70 | ~spl3_96 | spl3_27 | ~spl3_69 | ~spl3_93),
% 0.21/0.51    inference(avatar_split_clause,[],[f1044,f878,f654,f360,f899,f659])).
% 0.21/0.51  fof(f659,plain,(
% 0.21/0.51    spl3_70 <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 0.21/0.51  fof(f360,plain,(
% 0.21/0.51    spl3_27 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.51  fof(f654,plain,(
% 0.21/0.51    spl3_69 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.21/0.51  fof(f878,plain,(
% 0.21/0.51    spl3_93 <=> ! [X8] : (~v1_funct_2(k2_funct_1(sK2),sK1,X8) | k1_xboole_0 = X8 | ~r1_tarski(X8,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X8))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 0.21/0.51  fof(f1044,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl3_69 | ~spl3_93)),
% 0.21/0.51    inference(resolution,[],[f879,f656])).
% 0.21/0.51  fof(f656,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl3_69),
% 0.21/0.51    inference(avatar_component_clause,[],[f654])).
% 0.21/0.51  fof(f879,plain,(
% 0.21/0.51    ( ! [X8] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X8))) | k1_xboole_0 = X8 | ~r1_tarski(X8,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK1,X8)) ) | ~spl3_93),
% 0.21/0.51    inference(avatar_component_clause,[],[f878])).
% 0.21/0.51  fof(f891,plain,(
% 0.21/0.51    ~spl3_8 | spl3_93 | spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f890,f138,f878,f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl3_8 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f890,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(X0,sK0) | k1_xboole_0 = X0 | ~v1_funct_1(k2_funct_1(sK2))) ) | spl3_7),
% 0.21/0.51    inference(resolution,[],[f140,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f55])).
% 0.21/0.51  fof(f880,plain,(
% 0.21/0.51    ~spl3_8 | spl3_93 | spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f871,f134,f878,f142])).
% 0.21/0.51  fof(f871,plain,(
% 0.21/0.51    ( ! [X8] : (~v1_funct_2(k2_funct_1(sK2),sK1,X8) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X8))) | ~r1_tarski(X8,sK0) | k1_xboole_0 = X8 | ~v1_funct_1(k2_funct_1(sK2))) ) | spl3_6),
% 0.21/0.51    inference(resolution,[],[f101,f136])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X1,X2) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f55])).
% 0.21/0.51  fof(f699,plain,(
% 0.21/0.51    spl3_76 | ~spl3_25 | ~spl3_72 | ~spl3_61),
% 0.21/0.51    inference(avatar_split_clause,[],[f674,f600,f676,f341,f696])).
% 0.21/0.51  fof(f600,plain,(
% 0.21/0.51    spl3_61 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.21/0.51  fof(f674,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl3_61),
% 0.21/0.51    inference(superposition,[],[f66,f602])).
% 0.21/0.51  fof(f602,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK2) | ~spl3_61),
% 0.21/0.51    inference(avatar_component_clause,[],[f600])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.51  fof(f662,plain,(
% 0.21/0.51    spl3_70 | ~spl3_58 | ~spl3_61),
% 0.21/0.51    inference(avatar_split_clause,[],[f614,f600,f564,f659])).
% 0.21/0.51  fof(f564,plain,(
% 0.21/0.51    spl3_58 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.21/0.51  fof(f614,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl3_58 | ~spl3_61)),
% 0.21/0.51    inference(backward_demodulation,[],[f566,f602])).
% 0.21/0.51  fof(f566,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_58),
% 0.21/0.51    inference(avatar_component_clause,[],[f564])).
% 0.21/0.51  fof(f657,plain,(
% 0.21/0.51    spl3_69 | ~spl3_57 | ~spl3_61),
% 0.21/0.51    inference(avatar_split_clause,[],[f613,f600,f559,f654])).
% 0.21/0.51  fof(f559,plain,(
% 0.21/0.51    spl3_57 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.21/0.51  fof(f613,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl3_57 | ~spl3_61)),
% 0.21/0.51    inference(backward_demodulation,[],[f561,f602])).
% 0.21/0.51  fof(f561,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_57),
% 0.21/0.51    inference(avatar_component_clause,[],[f559])).
% 0.21/0.51  fof(f603,plain,(
% 0.21/0.51    spl3_61 | ~spl3_1 | ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f598,f119,f109,f600])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl3_1 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f598,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK2) | (~spl3_1 | ~spl3_3)),
% 0.21/0.51    inference(forward_demodulation,[],[f595,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f595,plain,(
% 0.21/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f94,f121])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f581,plain,(
% 0.21/0.51    spl3_43 | ~spl3_38 | ~spl3_27 | ~spl3_54),
% 0.21/0.51    inference(avatar_split_clause,[],[f572,f539,f360,f429,f452])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    spl3_38 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.51  fof(f539,plain,(
% 0.21/0.51    spl3_54 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.51  fof(f572,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_funct_1(sK2) | ~spl3_54),
% 0.21/0.51    inference(superposition,[],[f66,f541])).
% 0.21/0.51  fof(f541,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_54),
% 0.21/0.51    inference(avatar_component_clause,[],[f539])).
% 0.21/0.51  fof(f576,plain,(
% 0.21/0.51    ~spl3_38 | ~spl3_27 | spl3_29 | ~spl3_24 | ~spl3_54),
% 0.21/0.51    inference(avatar_split_clause,[],[f575,f539,f337,f369,f360,f429])).
% 0.21/0.51  fof(f369,plain,(
% 0.21/0.51    spl3_29 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.51  fof(f337,plain,(
% 0.21/0.51    spl3_24 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.51  % (23841)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  fof(f575,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_24 | ~spl3_54)),
% 0.21/0.51    inference(forward_demodulation,[],[f570,f339])).
% 0.21/0.51  fof(f339,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f337])).
% 0.21/0.51  fof(f570,plain,(
% 0.21/0.51    k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_54),
% 0.21/0.51    inference(superposition,[],[f67,f541])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.51  fof(f567,plain,(
% 0.21/0.51    spl3_58 | ~spl3_40 | ~spl3_54),
% 0.21/0.51    inference(avatar_split_clause,[],[f547,f539,f438,f564])).
% 0.21/0.51  fof(f438,plain,(
% 0.21/0.51    spl3_40 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.51  fof(f547,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_40 | ~spl3_54)),
% 0.21/0.51    inference(backward_demodulation,[],[f440,f541])).
% 0.21/0.51  fof(f440,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~spl3_40),
% 0.21/0.51    inference(avatar_component_clause,[],[f438])).
% 0.21/0.51  fof(f562,plain,(
% 0.21/0.51    spl3_57 | ~spl3_39 | ~spl3_54),
% 0.21/0.51    inference(avatar_split_clause,[],[f546,f539,f433,f559])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    spl3_39 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.51  fof(f546,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_39 | ~spl3_54)),
% 0.21/0.51    inference(backward_demodulation,[],[f435,f541])).
% 0.21/0.51  fof(f435,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_39),
% 0.21/0.51    inference(avatar_component_clause,[],[f433])).
% 0.21/0.51  fof(f542,plain,(
% 0.21/0.51    spl3_54 | ~spl3_25 | ~spl3_5 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f537,f114,f129,f341,f539])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl3_5 <=> v1_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f537,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.51    inference(resolution,[],[f76,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f114])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    ~spl3_25 | ~spl3_5 | spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f462,f142,f129,f341])).
% 0.21/0.51  fof(f462,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_8),
% 0.21/0.51    inference(resolution,[],[f144,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~v1_funct_1(k2_funct_1(sK2)) | spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f142])).
% 0.21/0.51  fof(f460,plain,(
% 0.21/0.51    ~spl3_25 | ~spl3_5 | spl3_38),
% 0.21/0.51    inference(avatar_split_clause,[],[f457,f429,f129,f341])).
% 0.21/0.51  fof(f457,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_38),
% 0.21/0.51    inference(resolution,[],[f431,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f431,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK2)) | spl3_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f429])).
% 0.21/0.51  fof(f441,plain,(
% 0.21/0.51    ~spl3_38 | ~spl3_8 | spl3_40 | ~spl3_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f424,f337,f438,f142,f429])).
% 0.21/0.51  fof(f424,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_24),
% 0.21/0.51    inference(superposition,[],[f71,f339])).
% 0.21/0.51  fof(f436,plain,(
% 0.21/0.51    ~spl3_38 | ~spl3_8 | spl3_39 | ~spl3_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f423,f337,f433,f142,f429])).
% 0.21/0.51  fof(f423,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_24),
% 0.21/0.51    inference(superposition,[],[f72,f339])).
% 0.21/0.51  fof(f349,plain,(
% 0.21/0.51    ~spl3_3 | spl3_25),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f348])).
% 0.21/0.51  fof(f348,plain,(
% 0.21/0.51    $false | (~spl3_3 | spl3_25)),
% 0.21/0.51    inference(subsumption_resolution,[],[f121,f346])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_25),
% 0.21/0.51    inference(resolution,[],[f343,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | spl3_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f341])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    spl3_24 | ~spl3_25 | ~spl3_5 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f335,f114,f129,f341,f337])).
% 0.21/0.51  fof(f335,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.51    inference(resolution,[],[f75,f116])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    ~spl3_17 | spl3_21 | ~spl3_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f285,f217,f298,f258])).
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl3_15),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f282])).
% 0.21/0.51  % (23826)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl3_15),
% 0.21/0.51    inference(superposition,[],[f68,f218])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    ~spl3_15 | spl3_17),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f286])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    $false | (~spl3_15 | spl3_17)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f242,f277,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  % (23840)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_17),
% 0.21/0.51    inference(resolution,[],[f260,f93])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    ~v1_relat_1(k1_xboole_0) | spl3_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f258])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    spl3_15 | ~spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f231,f147,f217])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl3_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_9),
% 0.21/0.51    inference(resolution,[],[f225,f154])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_9),
% 0.21/0.51    inference(resolution,[],[f223,f87])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl3_9),
% 0.21/0.51    inference(resolution,[],[f174,f149])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0) | ~spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f147])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 = X0) ) | ~spl3_9),
% 0.21/0.51    inference(resolution,[],[f69,f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_9),
% 0.21/0.51    inference(resolution,[],[f92,f149])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~v1_xboole_0(X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f62,f147])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ~spl3_6 | ~spl3_7 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f56,f142,f138,f134])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f25])).
% 0.21/0.51  fof(f25,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f57,f129])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f59,f119])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f60,f114])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f61,f109])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (23837)------------------------------
% 0.21/0.51  % (23837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23837)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (23837)Memory used [KB]: 7164
% 0.21/0.51  % (23837)Time elapsed: 0.096 s
% 0.21/0.51  % (23837)------------------------------
% 0.21/0.51  % (23837)------------------------------
% 0.21/0.51  % (23821)Success in time 0.154 s
%------------------------------------------------------------------------------
