%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t88_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:52 EDT 2019

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  366 (1166 expanded)
%              Number of leaves         :   98 ( 557 expanded)
%              Depth                    :    9
%              Number of atoms          : 1094 (3324 expanded)
%              Number of equality atoms :   78 ( 153 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f542,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f156,f160,f164,f168,f172,f198,f202,f206,f210,f214,f218,f222,f226,f230,f231,f235,f236,f240,f241,f245,f249,f253,f257,f261,f265,f269,f273,f285,f286,f290,f294,f298,f302,f306,f310,f314,f319,f324,f328,f333,f338,f350,f354,f355,f359,f363,f367,f372,f377,f389,f393,f397,f401,f402,f406,f411,f416,f449,f453,f457,f461,f465,f469,f473,f474,f478,f482,f486,f487,f491,f495,f499,f500,f504,f508,f512,f513,f517,f521,f525,f529,f533,f537,f541])).

fof(f541,plain,
    ( spl5_144
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f418,f414,f539])).

fof(f539,plain,
    ( spl5_144
  <=> k1_relset_1(sK0,sK0,k2_funct_1(sK1)) = k1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f414,plain,
    ( spl5_98
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f418,plain,
    ( k1_relset_1(sK0,sK0,k2_funct_1(sK1)) = k1_relat_1(k2_funct_1(sK1))
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f415,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',redefinition_k1_relset_1)).

fof(f415,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_98 ),
    inference(avatar_component_clause,[],[f414])).

fof(f537,plain,
    ( spl5_142
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f419,f414,f535])).

fof(f535,plain,
    ( spl5_142
  <=> k2_relat_1(k2_funct_1(sK1)) = k2_relset_1(sK0,sK0,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f419,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k2_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f415,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',redefinition_k2_relset_1)).

fof(f533,plain,
    ( spl5_140
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f420,f414,f531])).

fof(f531,plain,
    ( spl5_140
  <=> m1_subset_1(k2_relset_1(sK0,sK0,k2_funct_1(sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f420,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK0,k2_funct_1(sK1)),k1_zfmisc_1(sK0))
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f415,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',dt_k2_relset_1)).

fof(f529,plain,
    ( spl5_138
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f421,f414,f527])).

fof(f527,plain,
    ( spl5_138
  <=> m1_subset_1(k1_relset_1(sK0,sK0,k2_funct_1(sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f421,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK0,k2_funct_1(sK1)),k1_zfmisc_1(sK0))
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f415,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',dt_k1_relset_1)).

fof(f525,plain,
    ( spl5_136
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f422,f414,f523])).

fof(f523,plain,
    ( spl5_136
  <=> v5_relat_1(k2_funct_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_136])])).

fof(f422,plain,
    ( v5_relat_1(k2_funct_1(sK1),sK0)
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f415,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',cc2_relset_1)).

fof(f521,plain,
    ( spl5_134
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f423,f414,f331,f296,f519])).

fof(f519,plain,
    ( spl5_134
  <=> v2_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f296,plain,
    ( spl5_56
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f331,plain,
    ( spl5_68
  <=> v3_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f423,plain,
    ( v2_funct_1(k2_funct_1(sK1))
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f332,f415,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',cc2_funct_2)).

fof(f332,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f331])).

fof(f297,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f296])).

fof(f517,plain,
    ( spl5_132
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f424,f414,f331,f296,f515])).

fof(f515,plain,
    ( spl5_132
  <=> v2_funct_2(k2_funct_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f424,plain,
    ( v2_funct_2(k2_funct_1(sK1),sK0)
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f332,f415,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f513,plain,
    ( spl5_128
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f425,f414,f296,f506])).

fof(f506,plain,
    ( spl5_128
  <=> k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f425,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK1))
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f297,f415,f415,f138])).

fof(f138,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',redefinition_k1_partfun1)).

fof(f512,plain,
    ( spl5_130
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f426,f414,f296,f170,f158,f510])).

fof(f510,plain,
    ( spl5_130
  <=> k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_130])])).

fof(f158,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f170,plain,
    ( spl5_10
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f426,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f171,f297,f159,f415,f138])).

fof(f159,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f171,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f508,plain,
    ( spl5_128
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f427,f414,f296,f506])).

fof(f427,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1)) = k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK1))
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f415,f297,f415,f138])).

fof(f504,plain,
    ( spl5_126
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f428,f414,f296,f170,f158,f502])).

fof(f502,plain,
    ( spl5_126
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f428,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f171,f159,f297,f415,f138])).

fof(f500,plain,
    ( spl5_122
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f429,f414,f296,f493])).

fof(f493,plain,
    ( spl5_122
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f429,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1)))
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f297,f415,f415,f139])).

fof(f139,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',dt_k1_partfun1)).

fof(f499,plain,
    ( spl5_124
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f430,f414,f296,f170,f158,f497])).

fof(f497,plain,
    ( spl5_124
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f430,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1))
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f171,f297,f159,f415,f139])).

fof(f495,plain,
    ( spl5_122
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f431,f414,f296,f493])).

fof(f431,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1)))
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f415,f297,f415,f139])).

fof(f491,plain,
    ( spl5_120
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f432,f414,f296,f170,f158,f489])).

fof(f489,plain,
    ( spl5_120
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f432,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)))
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f171,f159,f297,f415,f139])).

fof(f487,plain,
    ( spl5_116
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f433,f414,f296,f480])).

fof(f480,plain,
    ( spl5_116
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f433,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f297,f415,f415,f140])).

fof(f140,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f486,plain,
    ( spl5_118
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f434,f414,f296,f170,f158,f484])).

fof(f484,plain,
    ( spl5_118
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f434,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f171,f297,f159,f415,f140])).

fof(f482,plain,
    ( spl5_116
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f435,f414,f296,f480])).

fof(f435,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f415,f297,f415,f140])).

fof(f478,plain,
    ( spl5_114
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f436,f414,f296,f170,f158,f476])).

fof(f476,plain,
    ( spl5_114
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f436,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_56
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f171,f159,f297,f415,f140])).

fof(f474,plain,
    ( spl5_112
    | spl5_27
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f437,f414,f224,f471])).

fof(f471,plain,
    ( spl5_112
  <=> r2_relset_1(sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f224,plain,
    ( spl5_27
  <=> ~ sP4(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f437,plain,
    ( r2_relset_1(sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1))
    | ~ spl5_27
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f225,f415,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f147_D])).

fof(f147_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP4(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f225,plain,
    ( ~ sP4(sK0,sK0)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f224])).

fof(f473,plain,
    ( spl5_112
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f439,f414,f471])).

fof(f439,plain,
    ( r2_relset_1(sK0,sK0,k2_funct_1(sK1),k2_funct_1(sK1))
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f415,f149])).

fof(f149,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f137])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',redefinition_r2_relset_1)).

fof(f469,plain,
    ( spl5_110
    | ~ spl5_56
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f440,f414,f336,f296,f467])).

fof(f467,plain,
    ( spl5_110
  <=> k1_relset_1(sK0,sK0,k2_funct_1(sK1)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f336,plain,
    ( spl5_70
  <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f440,plain,
    ( k1_relset_1(sK0,sK0,k2_funct_1(sK1)) = sK0
    | ~ spl5_56
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f337,f415,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',t67_funct_2)).

fof(f337,plain,
    ( v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl5_70 ),
    inference(avatar_component_clause,[],[f336])).

fof(f465,plain,
    ( spl5_108
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f441,f414,f336,f331,f296,f463])).

fof(f463,plain,
    ( spl5_108
  <=> v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f441,plain,
    ( v1_funct_1(k2_funct_2(sK0,k2_funct_1(sK1)))
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f337,f332,f415,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',dt_k2_funct_2)).

fof(f461,plain,
    ( spl5_106
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f442,f414,f336,f331,f296,f459])).

fof(f459,plain,
    ( spl5_106
  <=> v1_funct_2(k2_funct_2(sK0,k2_funct_1(sK1)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f442,plain,
    ( v1_funct_2(k2_funct_2(sK0,k2_funct_1(sK1)),sK0,sK0)
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f337,f332,f415,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f457,plain,
    ( spl5_104
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f443,f414,f336,f331,f296,f455])).

fof(f455,plain,
    ( spl5_104
  <=> v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK1)),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f443,plain,
    ( v3_funct_2(k2_funct_2(sK0,k2_funct_1(sK1)),sK0,sK0)
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f337,f332,f415,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f453,plain,
    ( spl5_102
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f444,f414,f336,f331,f296,f451])).

fof(f451,plain,
    ( spl5_102
  <=> m1_subset_1(k2_funct_2(sK0,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f444,plain,
    ( m1_subset_1(k2_funct_2(sK0,k2_funct_1(sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f337,f332,f415,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f449,plain,
    ( spl5_100
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f445,f414,f336,f331,f296,f447])).

fof(f447,plain,
    ( spl5_100
  <=> k2_funct_2(sK0,k2_funct_1(sK1)) = k2_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f445,plain,
    ( k2_funct_2(sK0,k2_funct_1(sK1)) = k2_funct_1(k2_funct_1(sK1))
    | ~ spl5_56
    | ~ spl5_68
    | ~ spl5_70
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f297,f337,f332,f415,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',redefinition_k2_funct_2)).

fof(f416,plain,
    ( spl5_98
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f412,f200,f196,f414])).

fof(f196,plain,
    ( spl5_12
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f200,plain,
    ( spl5_14
  <=> m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f412,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f201,f197])).

fof(f197,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f196])).

fof(f201,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f200])).

fof(f411,plain,
    ( spl5_96
    | ~ spl5_22
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f407,f267,f216,f409])).

fof(f409,plain,
    ( spl5_96
  <=> k1_relat_1(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f216,plain,
    ( spl5_22
  <=> k1_relset_1(sK0,sK0,sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f267,plain,
    ( spl5_46
  <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f407,plain,
    ( k1_relat_1(sK1) = sK0
    | ~ spl5_22
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f268,f217])).

fof(f217,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f216])).

fof(f268,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f267])).

fof(f406,plain,
    ( spl5_94
    | ~ spl5_50
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f378,f300,f283,f404])).

fof(f404,plain,
    ( spl5_94
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK1,sK1),k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f283,plain,
    ( spl5_50
  <=> v1_relat_1(k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f300,plain,
    ( spl5_58
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f378,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK1,sK1),k2_funct_1(sK1)))
    | ~ spl5_50
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f301,f284,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',dt_k5_relat_1)).

fof(f284,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK1))
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f283])).

fof(f301,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f300])).

fof(f402,plain,
    ( spl5_88
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f379,f283,f391])).

fof(f391,plain,
    ( spl5_88
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK1,sK1),k5_relat_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f379,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK1,sK1),k5_relat_1(sK1,sK1)))
    | ~ spl5_50 ),
    inference(unit_resulting_resolution,[],[f284,f284,f112])).

fof(f401,plain,
    ( spl5_92
    | ~ spl5_48
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f381,f283,f271,f399])).

fof(f399,plain,
    ( spl5_92
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK1,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f271,plain,
    ( spl5_48
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f381,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK1,sK1),sK1))
    | ~ spl5_48
    | ~ spl5_50 ),
    inference(unit_resulting_resolution,[],[f272,f284,f112])).

fof(f272,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f271])).

fof(f397,plain,
    ( spl5_90
    | ~ spl5_50
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f382,f300,f283,f395])).

fof(f395,plain,
    ( spl5_90
  <=> v1_relat_1(k5_relat_1(k2_funct_1(sK1),k5_relat_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f382,plain,
    ( v1_relat_1(k5_relat_1(k2_funct_1(sK1),k5_relat_1(sK1,sK1)))
    | ~ spl5_50
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f301,f284,f112])).

fof(f393,plain,
    ( spl5_88
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f383,f283,f391])).

fof(f383,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK1,sK1),k5_relat_1(sK1,sK1)))
    | ~ spl5_50 ),
    inference(unit_resulting_resolution,[],[f284,f284,f112])).

fof(f389,plain,
    ( spl5_86
    | ~ spl5_48
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f385,f283,f271,f387])).

fof(f387,plain,
    ( spl5_86
  <=> v1_relat_1(k5_relat_1(sK1,k5_relat_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f385,plain,
    ( v1_relat_1(k5_relat_1(sK1,k5_relat_1(sK1,sK1)))
    | ~ spl5_48
    | ~ spl5_50 ),
    inference(unit_resulting_resolution,[],[f272,f284,f112])).

fof(f377,plain,
    ( spl5_84
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f373,f263,f259,f375])).

fof(f375,plain,
    ( spl5_84
  <=> m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f259,plain,
    ( spl5_42
  <=> m1_subset_1(k2_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f263,plain,
    ( spl5_44
  <=> k2_relat_1(sK1) = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f373,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl5_42
    | ~ spl5_44 ),
    inference(backward_demodulation,[],[f264,f260])).

fof(f260,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f259])).

fof(f264,plain,
    ( k2_relat_1(sK1) = k2_relset_1(sK0,sK0,sK1)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f263])).

fof(f372,plain,
    ( spl5_82
    | ~ spl5_22
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f368,f255,f216,f370])).

fof(f370,plain,
    ( spl5_82
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f255,plain,
    ( spl5_40
  <=> m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f368,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl5_22
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f256,f217])).

fof(f256,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f255])).

fof(f367,plain,
    ( spl5_80
    | ~ spl5_56
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f339,f300,f296,f365])).

fof(f365,plain,
    ( spl5_80
  <=> v1_relat_1(k2_funct_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f339,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK1)))
    | ~ spl5_56
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f297,f301,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',dt_k2_funct_1)).

fof(f363,plain,
    ( spl5_78
    | ~ spl5_56
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f340,f300,f296,f361])).

fof(f361,plain,
    ( spl5_78
  <=> v1_funct_1(k2_funct_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f340,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK1)))
    | ~ spl5_56
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f297,f301,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f359,plain,
    ( spl5_76
    | ~ spl5_48
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f342,f300,f271,f357])).

fof(f357,plain,
    ( spl5_76
  <=> v1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f342,plain,
    ( v1_relat_1(k5_relat_1(k2_funct_1(sK1),sK1))
    | ~ spl5_48
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f272,f301,f112])).

fof(f355,plain,
    ( spl5_72
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f343,f300,f348])).

fof(f348,plain,
    ( spl5_72
  <=> v1_relat_1(k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f343,plain,
    ( v1_relat_1(k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK1)))
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f301,f301,f112])).

fof(f354,plain,
    ( spl5_74
    | ~ spl5_48
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f345,f300,f271,f352])).

fof(f352,plain,
    ( spl5_74
  <=> v1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f345,plain,
    ( v1_relat_1(k5_relat_1(sK1,k2_funct_1(sK1)))
    | ~ spl5_48
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f272,f301,f112])).

fof(f350,plain,
    ( spl5_72
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f346,f300,f348])).

fof(f346,plain,
    ( v1_relat_1(k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK1)))
    | ~ spl5_58 ),
    inference(unit_resulting_resolution,[],[f301,f301,f112])).

fof(f338,plain,
    ( spl5_70
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f334,f208,f196,f336])).

fof(f208,plain,
    ( spl5_18
  <=> v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f334,plain,
    ( v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f209,f197])).

fof(f209,plain,
    ( v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f208])).

fof(f333,plain,
    ( spl5_68
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f329,f204,f196,f331])).

fof(f204,plain,
    ( spl5_16
  <=> v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f329,plain,
    ( v3_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f205,f197])).

fof(f205,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f204])).

fof(f328,plain,
    ( ~ spl5_67
    | spl5_1
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f323,f196,f151,f326])).

fof(f326,plain,
    ( spl5_67
  <=> ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f151,plain,
    ( spl5_1
  <=> ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f323,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ spl5_1
    | ~ spl5_12 ),
    inference(backward_demodulation,[],[f197,f152])).

fof(f152,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f151])).

fof(f324,plain,
    ( spl5_56
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f322,f212,f196,f296])).

fof(f212,plain,
    ( spl5_20
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f322,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl5_12
    | ~ spl5_20 ),
    inference(backward_demodulation,[],[f197,f213])).

fof(f213,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f212])).

fof(f319,plain,
    ( spl5_64
    | ~ spl5_34
    | ~ spl5_38
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f315,f271,f251,f243,f317])).

fof(f317,plain,
    ( spl5_64
  <=> k2_relat_1(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f243,plain,
    ( spl5_34
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f251,plain,
    ( spl5_38
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f315,plain,
    ( k2_relat_1(sK1) = sK0
    | ~ spl5_34
    | ~ spl5_38
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f272,f244,f252,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',d3_funct_2)).

fof(f252,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f251])).

fof(f244,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f243])).

fof(f314,plain,
    ( spl5_62
    | spl5_27 ),
    inference(avatar_split_clause,[],[f303,f224,f312])).

fof(f312,plain,
    ( spl5_62
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f303,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f142,f225,f147])).

fof(f142,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f102,f101])).

fof(f101,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',redefinition_k6_partfun1)).

fof(f102,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',dt_k6_partfun1)).

fof(f310,plain,
    ( spl5_60
    | spl5_27 ),
    inference(avatar_split_clause,[],[f304,f224,f308])).

fof(f308,plain,
    ( spl5_60
  <=> r2_relset_1(sK0,sK0,sK2(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK2(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f304,plain,
    ( r2_relset_1(sK0,sK0,sK2(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK2(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f108,f225,f147])).

fof(f108,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',existence_m1_subset_1)).

fof(f306,plain,
    ( spl5_24
    | ~ spl5_4
    | spl5_27 ),
    inference(avatar_split_clause,[],[f305,f224,f158,f220])).

fof(f220,plain,
    ( spl5_24
  <=> r2_relset_1(sK0,sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f305,plain,
    ( r2_relset_1(sK0,sK0,sK1,sK1)
    | ~ spl5_4
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f159,f225,f147])).

fof(f302,plain,
    ( spl5_58
    | ~ spl5_10
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f274,f271,f170,f300])).

fof(f274,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl5_10
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f171,f272,f104])).

fof(f298,plain,
    ( spl5_56
    | ~ spl5_10
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f275,f271,f170,f296])).

fof(f275,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl5_10
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f171,f272,f105])).

fof(f294,plain,
    ( spl5_54
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f276,f271,f247,f170,f292])).

fof(f292,plain,
    ( spl5_54
  <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f247,plain,
    ( spl5_36
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f276,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_relat_1(k1_relat_1(sK1))
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f248,f171,f272,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',t61_funct_1)).

fof(f248,plain,
    ( v2_funct_1(sK1)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f247])).

fof(f290,plain,
    ( spl5_52
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f277,f271,f247,f170,f288])).

fof(f288,plain,
    ( spl5_52
  <=> k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f277,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_relat_1(k2_relat_1(sK1))
    | ~ spl5_10
    | ~ spl5_36
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f248,f171,f272,f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f286,plain,
    ( spl5_50
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f279,f271,f283])).

fof(f279,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK1))
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f272,f272,f112])).

fof(f285,plain,
    ( spl5_50
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f281,f271,f283])).

fof(f281,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK1))
    | ~ spl5_48 ),
    inference(unit_resulting_resolution,[],[f272,f272,f112])).

fof(f273,plain,
    ( spl5_48
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f173,f158,f271])).

fof(f173,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f159,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',cc1_relset_1)).

fof(f269,plain,
    ( spl5_46
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f174,f158,f267])).

fof(f174,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f159,f124])).

fof(f265,plain,
    ( spl5_44
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f175,f158,f263])).

fof(f175,plain,
    ( k2_relat_1(sK1) = k2_relset_1(sK0,sK0,sK1)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f159,f125])).

fof(f261,plain,
    ( spl5_42
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f176,f158,f259])).

fof(f176,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f159,f126])).

fof(f257,plain,
    ( spl5_40
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f177,f158,f255])).

fof(f177,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f159,f127])).

fof(f253,plain,
    ( spl5_38
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f178,f158,f251])).

fof(f178,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f159,f128])).

fof(f249,plain,
    ( spl5_36
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f179,f170,f162,f158,f247])).

fof(f162,plain,
    ( spl5_6
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f179,plain,
    ( v2_funct_1(sK1)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f163,f159,f130])).

fof(f163,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f245,plain,
    ( spl5_34
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f180,f170,f162,f158,f243])).

fof(f180,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f163,f159,f131])).

fof(f241,plain,
    ( spl5_32
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f181,f170,f158,f238])).

fof(f238,plain,
    ( spl5_32
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f181,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f171,f159,f159,f138])).

fof(f240,plain,
    ( spl5_32
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f182,f170,f158,f238])).

fof(f182,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f171,f159,f159,f138])).

fof(f236,plain,
    ( spl5_30
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f183,f170,f158,f233])).

fof(f233,plain,
    ( spl5_30
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f183,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f171,f159,f159,f139])).

fof(f235,plain,
    ( spl5_30
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f184,f170,f158,f233])).

fof(f184,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f171,f159,f159,f139])).

fof(f231,plain,
    ( spl5_28
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f185,f170,f158,f228])).

fof(f228,plain,
    ( spl5_28
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f185,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f171,f159,f159,f140])).

fof(f230,plain,
    ( spl5_28
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f186,f170,f158,f228])).

fof(f186,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f171,f159,f159,f140])).

fof(f226,plain,
    ( ~ spl5_27
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f187,f158,f224])).

fof(f187,plain,
    ( ~ sP4(sK0,sK0)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f159,f148])).

fof(f148,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(general_splitting,[],[f134,f147_D])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',reflexivity_r2_relset_1)).

fof(f222,plain,
    ( spl5_24
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f188,f158,f220])).

fof(f188,plain,
    ( r2_relset_1(sK0,sK0,sK1,sK1)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f159,f149])).

fof(f218,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f189,f170,f166,f158,f216])).

fof(f166,plain,
    ( spl5_8
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f189,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f167,f159,f120])).

fof(f167,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f166])).

fof(f214,plain,
    ( spl5_20
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f190,f170,f166,f162,f158,f212])).

fof(f190,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f167,f163,f159,f116])).

fof(f210,plain,
    ( spl5_18
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f191,f170,f166,f162,f158,f208])).

fof(f191,plain,
    ( v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f167,f163,f159,f117])).

fof(f206,plain,
    ( spl5_16
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f192,f170,f166,f162,f158,f204])).

fof(f192,plain,
    ( v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f167,f163,f159,f118])).

fof(f202,plain,
    ( spl5_14
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f193,f170,f166,f162,f158,f200])).

fof(f193,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f167,f163,f159,f119])).

fof(f198,plain,
    ( spl5_12
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f194,f170,f166,f162,f158,f196])).

fof(f194,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f171,f167,f163,f159,f115])).

fof(f172,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f94,f170])).

fof(f94,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f88])).

fof(f88,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t88_funct_2.p',t88_funct_2)).

fof(f168,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f95,f166])).

fof(f95,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f89])).

fof(f164,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f96,f162])).

fof(f96,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f89])).

fof(f160,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f97,f158])).

fof(f97,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f89])).

fof(f156,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f141,f154,f151])).

fof(f154,plain,
    ( spl5_3
  <=> ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f141,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f98,f101,f101])).

fof(f98,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f89])).
%------------------------------------------------------------------------------
