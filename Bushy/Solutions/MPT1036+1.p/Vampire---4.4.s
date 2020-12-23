%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t146_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:31 EDT 2019

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  848 (2885 expanded)
%              Number of leaves         :  174 (1178 expanded)
%              Depth                    :   18
%              Number of atoms          : 3733 (10070 expanded)
%              Number of equality atoms :  275 (1217 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3867,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f93,f100,f107,f114,f127,f134,f141,f145,f166,f173,f183,f200,f227,f238,f245,f252,f265,f288,f292,f303,f310,f312,f314,f318,f327,f328,f341,f407,f411,f419,f437,f492,f503,f516,f528,f546,f550,f555,f557,f568,f603,f624,f631,f681,f733,f773,f827,f837,f879,f950,f965,f976,f1046,f1053,f1060,f1064,f1166,f1176,f1183,f1192,f1197,f1204,f1213,f1214,f1215,f1225,f1229,f1237,f1245,f1255,f1260,f1267,f1313,f1333,f1396,f1405,f1471,f1528,f1607,f1651,f1658,f1671,f1677,f1696,f1703,f1720,f1748,f1774,f1784,f1788,f1798,f1836,f1844,f1846,f1971,f2022,f2030,f2037,f2044,f2095,f2102,f2109,f2123,f2130,f2142,f2183,f2185,f2220,f2227,f2231,f2238,f2251,f2262,f2308,f2315,f2322,f2329,f2330,f2337,f2344,f2354,f2361,f2369,f2376,f2385,f2395,f2402,f2411,f2426,f2430,f2443,f2562,f2629,f2716,f2726,f2728,f2732,f2853,f2875,f2987,f3003,f3132,f3225,f3249,f3254,f3256,f3259,f3316,f3371,f3388,f3448,f3449,f3450,f3451,f3452,f3453,f3491,f3495,f3502,f3537,f3603,f3686,f3865])).

fof(f3865,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | spl6_15
    | ~ spl6_40
    | spl6_43
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(avatar_contradiction_clause,[],[f3864])).

fof(f3864,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_40
    | ~ spl6_43
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f3856,f133])).

fof(f133,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_15
  <=> k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f3856,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_40
    | ~ spl6_43
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(resolution,[],[f3824,f255])).

fof(f255,plain,
    ( m1_subset_1(sK3,k1_relat_1(sK1))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl6_40
  <=> m1_subset_1(sK3,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f3824,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_relat_1(sK1))
        | k1_funct_1(sK1,X9) = k1_funct_1(sK2,X9) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_43
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f3823,f117])).

fof(f117,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_10
  <=> r1_partfun1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f3823,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_relat_1(sK1))
        | k1_funct_1(sK1,X9) = k1_funct_1(sK2,X9)
        | ~ r1_partfun1(sK1,sK2) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_43
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f3822,f680])).

fof(f680,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f679])).

fof(f679,plain,
    ( spl6_80
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f3822,plain,
    ( ! [X9] :
        ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X9,k1_relat_1(sK1))
        | k1_funct_1(sK1,X9) = k1_funct_1(sK2,X9)
        | ~ r1_partfun1(sK1,sK2) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_43
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f3814,f85])).

fof(f85,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f3814,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X9,k1_relat_1(sK1))
        | k1_funct_1(sK1,X9) = k1_funct_1(sK2,X9)
        | ~ r1_partfun1(sK1,sK2) )
    | ~ spl6_2
    | ~ spl6_43
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(resolution,[],[f3713,f772])).

fof(f772,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f771])).

fof(f771,plain,
    ( spl6_84
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f3713,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X1,k1_relat_1(sK1))
        | k1_funct_1(sK1,X1) = k1_funct_1(X2,X1)
        | ~ r1_partfun1(sK1,X2) )
    | ~ spl6_2
    | ~ spl6_43
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f3712,f261])).

fof(f261,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl6_43
  <=> ~ v1_xboole_0(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f3712,plain,
    ( ! [X2,X1] :
        ( v1_xboole_0(k1_relat_1(sK1))
        | ~ m1_subset_1(X1,k1_relat_1(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK1,X1) = k1_funct_1(X2,X1)
        | ~ r1_partfun1(sK1,X2) )
    | ~ spl6_2
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(forward_demodulation,[],[f3711,f1059])).

fof(f1059,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_relat_1(sK1)
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f1058,plain,
    ( spl6_98
  <=> k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f3711,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_relat_1(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK1,X1) = k1_funct_1(X2,X1)
        | ~ r1_partfun1(sK1,X2)
        | v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)) )
    | ~ spl6_2
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f3710,f878])).

fof(f878,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f877])).

fof(f877,plain,
    ( spl6_88
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f3710,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_relat_1(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK1,X1) = k1_funct_1(X2,X1)
        | ~ r1_partfun1(sK1,X2)
        | v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) )
    | ~ spl6_2
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f3689,f92])).

fof(f92,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f3689,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_relat_1(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(sK1)
        | k1_funct_1(sK1,X1) = k1_funct_1(X2,X1)
        | ~ r1_partfun1(sK1,X2)
        | v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) )
    | ~ spl6_98 ),
    inference(superposition,[],[f211,f1059])).

fof(f211,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_relset_1(k1_xboole_0,X1,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,X3) = k1_funct_1(X2,X3)
      | ~ r1_partfun1(X0,X2)
      | v1_xboole_0(k1_relset_1(k1_xboole_0,X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(resolution,[],[f79,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',t2_subset)).

fof(f79,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
      | ~ r1_partfun1(X2,X3) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
      | ~ r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',t145_funct_2)).

fof(f3686,plain,
    ( spl6_96
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f3552,f526,f514,f1048])).

fof(f1048,plain,
    ( spl6_96
  <=> m1_subset_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f514,plain,
    ( spl6_66
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f526,plain,
    ( spl6_68
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f3552,plain,
    ( m1_subset_1(sK3,k1_xboole_0)
    | ~ spl6_66
    | ~ spl6_68 ),
    inference(backward_demodulation,[],[f515,f527])).

fof(f527,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f526])).

fof(f515,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f514])).

fof(f3603,plain,
    ( ~ spl6_66
    | ~ spl6_68
    | spl6_77
    | spl6_183 ),
    inference(avatar_contradiction_clause,[],[f3602])).

fof(f3602,plain,
    ( $false
    | ~ spl6_66
    | ~ spl6_68
    | ~ spl6_77
    | ~ spl6_183 ),
    inference(subsumption_resolution,[],[f3552,f3515])).

fof(f3515,plain,
    ( ~ m1_subset_1(sK3,k1_xboole_0)
    | ~ spl6_77
    | ~ spl6_183 ),
    inference(subsumption_resolution,[],[f2180,f599])).

fof(f599,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f598])).

fof(f598,plain,
    ( spl6_77
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f2180,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_xboole_0)
    | ~ spl6_183 ),
    inference(resolution,[],[f1970,f68])).

fof(f1970,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | ~ spl6_183 ),
    inference(avatar_component_clause,[],[f1969])).

fof(f1969,plain,
    ( spl6_183
  <=> ~ r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_183])])).

fof(f3537,plain,
    ( spl6_77
    | ~ spl6_96
    | spl6_183 ),
    inference(avatar_contradiction_clause,[],[f3536])).

fof(f3536,plain,
    ( $false
    | ~ spl6_77
    | ~ spl6_96
    | ~ spl6_183 ),
    inference(subsumption_resolution,[],[f1049,f3515])).

fof(f1049,plain,
    ( m1_subset_1(sK3,k1_xboole_0)
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f1048])).

fof(f3502,plain,
    ( spl6_15
    | ~ spl6_28
    | ~ spl6_270 ),
    inference(avatar_contradiction_clause,[],[f3501])).

fof(f3501,plain,
    ( $false
    | ~ spl6_15
    | ~ spl6_28
    | ~ spl6_270 ),
    inference(subsumption_resolution,[],[f3499,f133])).

fof(f3499,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl6_28
    | ~ spl6_270 ),
    inference(resolution,[],[f3490,f196])).

fof(f196,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_28
  <=> r2_hidden(sK3,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f3490,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4) )
    | ~ spl6_270 ),
    inference(avatar_component_clause,[],[f3489])).

fof(f3489,plain,
    ( spl6_270
  <=> ! [X4] :
        ( k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
        | ~ r2_hidden(X4,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_270])])).

fof(f3495,plain,
    ( ~ spl6_28
    | ~ spl6_62 ),
    inference(avatar_contradiction_clause,[],[f3494])).

fof(f3494,plain,
    ( $false
    | ~ spl6_28
    | ~ spl6_62 ),
    inference(resolution,[],[f502,f196])).

fof(f502,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_relat_1(sK1))
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f501])).

fof(f501,plain,
    ( spl6_62
  <=> ! [X1] : ~ r2_hidden(X1,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f3491,plain,
    ( spl6_270
    | ~ spl6_11
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_118 ),
    inference(avatar_split_clause,[],[f3266,f1243,f105,f98,f84,f119,f3489])).

fof(f119,plain,
    ( spl6_11
  <=> ~ r1_partfun1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f98,plain,
    ( spl6_4
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f105,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1243,plain,
    ( spl6_118
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ r1_partfun1(sK1,X1)
        | k1_funct_1(sK1,X0) = k1_funct_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X1,sK0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f3266,plain,
    ( ! [X4] :
        ( ~ r1_partfun1(sK1,sK2)
        | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
        | ~ r2_hidden(X4,k1_relat_1(sK1)) )
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_118 ),
    inference(subsumption_resolution,[],[f3265,f99])).

fof(f99,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f3265,plain,
    ( ! [X4] :
        ( ~ r1_partfun1(sK1,sK2)
        | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
        | ~ r2_hidden(X4,k1_relat_1(sK1))
        | ~ v1_funct_2(sK2,sK0,sK0) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_118 ),
    inference(subsumption_resolution,[],[f1248,f85])).

fof(f1248,plain,
    ( ! [X4] :
        ( ~ r1_partfun1(sK1,sK2)
        | k1_funct_1(sK1,X4) = k1_funct_1(sK2,X4)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X4,k1_relat_1(sK1))
        | ~ v1_funct_2(sK2,sK0,sK0) )
    | ~ spl6_6
    | ~ spl6_118 ),
    inference(resolution,[],[f1244,f106])).

fof(f106,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f1244,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK1,X1)
        | k1_funct_1(sK1,X0) = k1_funct_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_funct_2(X1,sK0,sK0) )
    | ~ spl6_118 ),
    inference(avatar_component_clause,[],[f1243])).

fof(f3453,plain,
    ( spl6_66
    | spl6_116
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38
    | spl6_43 ),
    inference(avatar_split_clause,[],[f3260,f260,f250,f112,f91,f1235,f514])).

fof(f1235,plain,
    ( spl6_116
  <=> ! [X7,X8] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK1))
        | ~ r1_partfun1(sK1,X8)
        | k1_funct_1(sK1,X7) = k1_funct_1(X8,X7)
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X8,sK0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f112,plain,
    ( spl6_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f250,plain,
    ( spl6_38
  <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f3260,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK1))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK1,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK1,X8) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f634,f261])).

fof(f634,plain,
    ( ! [X8,X7] :
        ( v1_xboole_0(k1_relat_1(sK1))
        | ~ m1_subset_1(X7,k1_relat_1(sK1))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK1,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK1,X8) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f633,f251])).

fof(f251,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f250])).

fof(f633,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK1))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK1,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK1,X8)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK1)) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f632,f113])).

fof(f113,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f632,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK1))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK1,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK1,X8)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f618,f92])).

fof(f618,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK1))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK1)
        | k1_funct_1(sK1,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK1,X8)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_38 ),
    inference(superposition,[],[f228,f251])).

fof(f228,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_relset_1(X1,X2,X0))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,X4) = k1_funct_1(X3,X4)
      | ~ r1_partfun1(X0,X3)
      | v1_xboole_0(k1_relset_1(X1,X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f56,f68])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
      | ~ r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3452,plain,
    ( spl6_102
    | ~ spl6_8
    | ~ spl6_38
    | spl6_43 ),
    inference(avatar_split_clause,[],[f1212,f260,f250,f112,f1181])).

fof(f1181,plain,
    ( spl6_102
  <=> m1_subset_1(sK5(k1_relat_1(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f1212,plain,
    ( m1_subset_1(sK5(k1_relat_1(sK1)),sK0)
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_43 ),
    inference(resolution,[],[f521,f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',existence_m1_subset_1)).

fof(f521,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK1))
        | m1_subset_1(X0,sK0) )
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f519,f261])).

fof(f519,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | v1_xboole_0(k1_relat_1(sK1))
        | ~ m1_subset_1(X0,k1_relat_1(sK1)) )
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(resolution,[],[f364,f68])).

fof(f364,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | m1_subset_1(X1,sK0) )
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f361,f113])).

fof(f361,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | m1_subset_1(X1,sK0) )
    | ~ spl6_38 ),
    inference(superposition,[],[f175,f251])).

fof(f175,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X7,k1_relset_1(X5,X6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | m1_subset_1(X7,X5) ) ),
    inference(resolution,[],[f71,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',t4_subset)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',dt_k1_relset_1)).

fof(f3451,plain,
    ( spl6_66
    | spl6_120
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36
    | spl6_111 ),
    inference(avatar_split_clause,[],[f1894,f1217,f243,f105,f84,f1253,f514])).

fof(f1253,plain,
    ( spl6_120
  <=> ! [X7,X8] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK2))
        | ~ r1_partfun1(sK2,X8)
        | k1_funct_1(sK2,X7) = k1_funct_1(X8,X7)
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X8,sK0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f243,plain,
    ( spl6_36
  <=> k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f1217,plain,
    ( spl6_111
  <=> ~ v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f1894,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK2))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK2,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK2,X8) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_111 ),
    inference(subsumption_resolution,[],[f1893,f1218])).

fof(f1218,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl6_111 ),
    inference(avatar_component_clause,[],[f1217])).

fof(f1893,plain,
    ( ! [X8,X7] :
        ( v1_xboole_0(k1_relat_1(sK2))
        | ~ m1_subset_1(X7,k1_relat_1(sK2))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK2,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK2,X8) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f1892,f244])).

fof(f244,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f243])).

fof(f1892,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK2))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK2,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK2,X8)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK2)) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f1891,f106])).

fof(f1891,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK2))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK2,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK2,X8)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_0
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f1117,f85])).

fof(f1117,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK2))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | k1_funct_1(sK2,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK2,X8)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_36 ),
    inference(superposition,[],[f228,f244])).

fof(f3450,plain,
    ( spl6_66
    | spl6_92
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f1905,f243,f105,f84,f974,f514])).

fof(f974,plain,
    ( spl6_92
  <=> ! [X0] :
        ( m1_subset_1(sK4(sK0,sK0,sK2,X0),k1_relat_1(sK2))
        | r1_partfun1(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f1905,plain,
    ( ! [X6] :
        ( m1_subset_1(sK4(sK0,sK0,sK2,X6),k1_relat_1(sK2))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,sK0,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X6) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f1904,f106])).

fof(f1904,plain,
    ( ! [X6] :
        ( m1_subset_1(sK4(sK0,sK0,sK2,X6),k1_relat_1(sK2))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,sK0,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X6)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_0
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f1116,f85])).

fof(f1116,plain,
    ( ! [X6] :
        ( m1_subset_1(sK4(sK0,sK0,sK2,X6),k1_relat_1(sK2))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,sK0,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X6)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_36 ),
    inference(superposition,[],[f209,f244])).

fof(f209,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(sK4(X5,X6,X4,X7),k1_relset_1(X5,X6,X4))
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,X5,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k1_xboole_0 = X6
      | ~ v1_funct_1(X4)
      | r1_partfun1(X4,X7)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f57,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',t1_subset)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X2)
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3449,plain,
    ( spl6_66
    | spl6_86
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f1903,f243,f105,f84,f835,f514])).

fof(f835,plain,
    ( spl6_86
  <=> ! [X0] :
        ( ~ r2_hidden(k1_relat_1(sK2),sK4(sK0,sK0,sK2,X0))
        | r1_partfun1(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f1903,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k1_relat_1(sK2),sK4(sK0,sK0,sK2,X5))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,sK0,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X5) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f1902,f106])).

fof(f1902,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k1_relat_1(sK2),sK4(sK0,sK0,sK2,X5))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,sK0,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X5)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_0
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f1115,f85])).

fof(f1115,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k1_relat_1(sK2),sK4(sK0,sK0,sK2,X5))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,sK0,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X5)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_36 ),
    inference(superposition,[],[f208,f244])).

fof(f208,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k1_relset_1(X1,X2,X0),sK4(X1,X2,X0,X3))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X0)
      | r1_partfun1(X0,X3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f57,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',antisymmetry_r2_hidden)).

fof(f3448,plain,
    ( spl6_66
    | spl6_82
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f1901,f243,f105,f84,f731,f514])).

fof(f731,plain,
    ( spl6_82
  <=> ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK2,X2),k1_relat_1(sK2))
        | r1_partfun1(sK2,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f1901,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK2,X2),k1_relat_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X2) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f1900,f85])).

fof(f1900,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK2,X2),k1_relat_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X2) )
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f1111,f106])).

fof(f1111,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK2,X2),k1_relat_1(sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X2) )
    | ~ spl6_36 ),
    inference(superposition,[],[f57,f244])).

fof(f3388,plain,
    ( spl6_66
    | spl6_78
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f1897,f105,f98,f84,f629,f514])).

fof(f629,plain,
    ( spl6_78
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X0))
        | r1_partfun1(X0,sK2)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1897,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f1896,f99])).

fof(f1896,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f1097,f85])).

fof(f1097,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f106,f210])).

fof(f210,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,X9,X10)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k1_xboole_0 = X10
      | ~ v1_funct_1(X8)
      | r1_partfun1(X8,X11)
      | ~ v1_xboole_0(k1_relset_1(X9,X10,X8)) ) ),
    inference(resolution,[],[f57,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',t7_boole)).

fof(f3371,plain,
    ( ~ spl6_269
    | spl6_57
    | spl6_59
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f3357,f526,f487,f402,f3369])).

fof(f3369,plain,
    ( spl6_269
  <=> ~ m1_subset_1(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_269])])).

fof(f402,plain,
    ( spl6_57
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f487,plain,
    ( spl6_59
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f3357,plain,
    ( ~ m1_subset_1(sK0,sK3)
    | ~ spl6_57
    | ~ spl6_59
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3356,f488])).

fof(f488,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f487])).

fof(f3356,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK3)
    | ~ spl6_57
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f3355,f403])).

fof(f403,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f402])).

fof(f3355,plain,
    ( v1_xboole_0(sK3)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK3)
    | ~ spl6_68 ),
    inference(resolution,[],[f527,f331])).

fof(f331,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f148,f68])).

fof(f148,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f68,f70])).

fof(f3316,plain,
    ( spl6_10
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f415,f308,f181,f164,f91,f84,f116])).

fof(f164,plain,
    ( spl6_20
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f181,plain,
    ( spl6_26
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f308,plain,
    ( spl6_48
  <=> r1_partfun1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f415,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f414,f165])).

fof(f165,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f164])).

fof(f414,plain,
    ( ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_26
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f413,f92])).

fof(f413,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_26
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f412,f182])).

fof(f182,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f181])).

fof(f412,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f320,f85])).

fof(f320,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_48 ),
    inference(resolution,[],[f309,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( r1_partfun1(X0,X1)
       => r1_partfun1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',symmetry_r1_partfun1)).

fof(f309,plain,
    ( r1_partfun1(sK2,sK1)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f308])).

fof(f3259,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_11
    | ~ spl6_46
    | ~ spl6_66
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98
    | spl6_169 ),
    inference(avatar_contradiction_clause,[],[f3258])).

fof(f3258,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_46
    | ~ spl6_66
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98
    | ~ spl6_169 ),
    inference(subsumption_resolution,[],[f3257,f3252])).

fof(f3252,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_46
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f3251,f120])).

fof(f120,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f3251,plain,
    ( r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_46
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f3250,f85])).

fof(f3250,plain,
    ( ~ v1_funct_1(sK2)
    | r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ spl6_2
    | ~ spl6_46
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f2447,f680])).

fof(f2447,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK1,sK2)
    | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ spl6_2
    | ~ spl6_46
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(resolution,[],[f2254,f772])).

fof(f2254,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | r1_partfun1(sK1,X0)
        | k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,X0)) )
    | ~ spl6_2
    | ~ spl6_46
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(resolution,[],[f2211,f291])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) )
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl6_46
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f2211,plain,
    ( ! [X3] :
        ( m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK1,X3),k1_relat_1(sK1))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | r1_partfun1(sK1,X3) )
    | ~ spl6_2
    | ~ spl6_88
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f2210,f878])).

fof(f2210,plain,
    ( ! [X3] :
        ( m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK1,X3),k1_relat_1(sK1))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | r1_partfun1(sK1,X3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) )
    | ~ spl6_2
    | ~ spl6_98 ),
    inference(subsumption_resolution,[],[f2189,f92])).

fof(f2189,plain,
    ( ! [X3] :
        ( m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK1,X3),k1_relat_1(sK1))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(sK1)
        | r1_partfun1(sK1,X3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) )
    | ~ spl6_98 ),
    inference(superposition,[],[f206,f1059])).

fof(f206,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(sK4(k1_xboole_0,X4,X3,X5),k1_relset_1(k1_xboole_0,X4,X3))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k1_xboole_0,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
      | ~ v1_funct_1(X3)
      | r1_partfun1(X3,X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4))) ) ),
    inference(resolution,[],[f78,f69])).

fof(f78,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK4(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2)
      | r1_partfun1(X2,X3) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3257,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ spl6_66
    | ~ spl6_169 ),
    inference(forward_demodulation,[],[f1744,f515])).

fof(f1744,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) != k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ spl6_169 ),
    inference(avatar_component_clause,[],[f1743])).

fof(f1743,plain,
    ( spl6_169
  <=> k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) != k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_169])])).

fof(f3256,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_11
    | ~ spl6_46
    | ~ spl6_66
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98
    | spl6_169 ),
    inference(avatar_contradiction_clause,[],[f3255])).

fof(f3255,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_46
    | ~ spl6_66
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98
    | ~ spl6_169 ),
    inference(subsumption_resolution,[],[f1944,f3252])).

fof(f1944,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ spl6_66
    | ~ spl6_169 ),
    inference(backward_demodulation,[],[f515,f1744])).

fof(f3254,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_11
    | ~ spl6_46
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98
    | spl6_267 ),
    inference(avatar_contradiction_clause,[],[f3253])).

fof(f3253,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_46
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_98
    | ~ spl6_267 ),
    inference(subsumption_resolution,[],[f3221,f3252])).

fof(f3221,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ spl6_267 ),
    inference(avatar_component_clause,[],[f3220])).

fof(f3220,plain,
    ( spl6_267
  <=> k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) != k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_267])])).

fof(f3249,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_11
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_266 ),
    inference(avatar_contradiction_clause,[],[f3248])).

fof(f3248,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_266 ),
    inference(subsumption_resolution,[],[f3247,f120])).

fof(f3247,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_266 ),
    inference(subsumption_resolution,[],[f3246,f92])).

fof(f3246,plain,
    ( ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_266 ),
    inference(subsumption_resolution,[],[f3245,f772])).

fof(f3245,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_80
    | ~ spl6_88
    | ~ spl6_266 ),
    inference(subsumption_resolution,[],[f3244,f680])).

fof(f3244,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_88
    | ~ spl6_266 ),
    inference(subsumption_resolution,[],[f3243,f85])).

fof(f3243,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_88
    | ~ spl6_266 ),
    inference(subsumption_resolution,[],[f3242,f878])).

fof(f3242,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_266 ),
    inference(trivial_inequality_removal,[],[f3240])).

fof(f3240,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) != k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_266 ),
    inference(superposition,[],[f77,f3224])).

fof(f3224,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ spl6_266 ),
    inference(avatar_component_clause,[],[f3223])).

fof(f3223,plain,
    ( spl6_266
  <=> k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_266])])).

fof(f77,plain,(
    ! [X2,X3,X1] :
      ( k1_funct_1(X2,sK4(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK4(k1_xboole_0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2)
      | r1_partfun1(X2,X3) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3225,plain,
    ( spl6_266
    | ~ spl6_66
    | ~ spl6_168 ),
    inference(avatar_split_clause,[],[f2175,f1746,f514,f3223])).

fof(f1746,plain,
    ( spl6_168
  <=> k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_168])])).

fof(f2175,plain,
    ( k1_funct_1(sK1,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2)) = k1_funct_1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK1,sK2))
    | ~ spl6_66
    | ~ spl6_168 ),
    inference(forward_demodulation,[],[f1747,f515])).

fof(f1747,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ spl6_168 ),
    inference(avatar_component_clause,[],[f1746])).

fof(f3132,plain,
    ( ~ spl6_263
    | spl6_264
    | spl6_77
    | ~ spl6_254 ),
    inference(avatar_split_clause,[],[f2989,f2873,f598,f3130,f3124])).

fof(f3124,plain,
    ( spl6_263
  <=> ~ m1_subset_1(k1_xboole_0,sK5(sK5(k1_zfmisc_1(k1_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_263])])).

fof(f3130,plain,
    ( spl6_264
  <=> v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_264])])).

fof(f2873,plain,
    ( spl6_254
  <=> m1_subset_1(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK2)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_254])])).

fof(f2989,plain,
    ( v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK2)))))
    | ~ m1_subset_1(k1_xboole_0,sK5(sK5(k1_zfmisc_1(k1_relat_1(sK2)))))
    | ~ spl6_77
    | ~ spl6_254 ),
    inference(subsumption_resolution,[],[f2988,f599])).

fof(f2988,plain,
    ( v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK2)))))
    | v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,sK5(sK5(k1_zfmisc_1(k1_relat_1(sK2)))))
    | ~ spl6_254 ),
    inference(resolution,[],[f2874,f331])).

fof(f2874,plain,
    ( m1_subset_1(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK2)))),k1_xboole_0)
    | ~ spl6_254 ),
    inference(avatar_component_clause,[],[f2873])).

fof(f3003,plain,
    ( ~ spl6_259
    | spl6_260
    | spl6_77
    | ~ spl6_246 ),
    inference(avatar_split_clause,[],[f2855,f2708,f598,f3001,f2995])).

fof(f2995,plain,
    ( spl6_259
  <=> ~ m1_subset_1(k1_xboole_0,sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_259])])).

fof(f3001,plain,
    ( spl6_260
  <=> v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_260])])).

fof(f2708,plain,
    ( spl6_246
  <=> m1_subset_1(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_246])])).

fof(f2855,plain,
    ( v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1)))))
    | ~ m1_subset_1(k1_xboole_0,sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1)))))
    | ~ spl6_77
    | ~ spl6_246 ),
    inference(subsumption_resolution,[],[f2854,f599])).

fof(f2854,plain,
    ( v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1)))))
    | v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1)))))
    | ~ spl6_246 ),
    inference(resolution,[],[f2709,f331])).

fof(f2709,plain,
    ( m1_subset_1(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1)))),k1_xboole_0)
    | ~ spl6_246 ),
    inference(avatar_component_clause,[],[f2708])).

fof(f2987,plain,
    ( spl6_76
    | spl6_256 ),
    inference(avatar_split_clause,[],[f1413,f2985,f601])).

fof(f601,plain,
    ( spl6_76
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f2985,plain,
    ( spl6_256
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ m1_subset_1(k1_xboole_0,sK4(k1_xboole_0,X1,X0,X2))
        | v1_xboole_0(sK4(k1_xboole_0,X1,X0,X2))
        | r1_partfun1(X0,X2)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_256])])).

fof(f1413,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X0)
      | r1_partfun1(X0,X2)
      | v1_xboole_0(sK4(k1_xboole_0,X1,X0,X2))
      | v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,sK4(k1_xboole_0,X1,X0,X2)) ) ),
    inference(resolution,[],[f363,f331])).

fof(f363,plain,(
    ! [X6,X4,X5] :
      ( m1_subset_1(sK4(k1_xboole_0,X5,X4,X6),k1_xboole_0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k1_xboole_0,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X4)
      | r1_partfun1(X4,X6) ) ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | m1_subset_1(sK4(k1_xboole_0,X5,X4,X6),k1_xboole_0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k1_xboole_0,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X4)
      | r1_partfun1(X4,X6) ) ),
    inference(resolution,[],[f175,f78])).

fof(f2875,plain,
    ( spl6_252
    | spl6_254
    | ~ spl6_66
    | ~ spl6_112 ),
    inference(avatar_split_clause,[],[f2615,f1223,f514,f2873,f2867])).

fof(f2867,plain,
    ( spl6_252
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_252])])).

fof(f1223,plain,
    ( spl6_112
  <=> ! [X0] :
        ( m1_subset_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).

fof(f2615,plain,
    ( m1_subset_1(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK2)))),k1_xboole_0)
    | v1_xboole_0(sK5(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl6_66
    | ~ spl6_112 ),
    inference(resolution,[],[f1926,f1336])).

fof(f1336,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK5(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK5(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f342,f76])).

fof(f342,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK5(k1_zfmisc_1(X1)))
      | v1_xboole_0(sK5(k1_zfmisc_1(X1)))
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f159,f68])).

fof(f159,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK5(k1_zfmisc_1(X3)))
      | m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f66,f76])).

fof(f1926,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK2))
        | m1_subset_1(X0,k1_xboole_0) )
    | ~ spl6_66
    | ~ spl6_112 ),
    inference(backward_demodulation,[],[f515,f1224])).

fof(f1224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK2))
        | m1_subset_1(X0,sK0) )
    | ~ spl6_112 ),
    inference(avatar_component_clause,[],[f1223])).

fof(f2853,plain,
    ( ~ spl6_77
    | spl6_250 ),
    inference(avatar_split_clause,[],[f1487,f2851,f598])).

fof(f2851,plain,
    ( spl6_250
  <=> ! [X3,X2] :
        ( ~ v1_funct_1(X2)
        | r1_partfun1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))),X2)
        | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
        | ~ v1_funct_2(X2,k1_xboole_0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_250])])).

fof(f1487,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
      | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))))
      | r1_partfun1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))),X2)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f378,f373])).

fof(f373,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k1_relat_1(sK5(k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
      | ~ v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f366,f76])).

fof(f366,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k1_relat_1(sK5(k1_zfmisc_1(k2_zfmisc_1(X3,X4)))))
      | ~ m1_subset_1(sK5(k1_zfmisc_1(k2_zfmisc_1(X3,X4))),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_xboole_0(X3) ) ),
    inference(superposition,[],[f176,f187])).

fof(f187,plain,(
    ! [X4,X5] : k1_relset_1(X4,X5,sK5(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) = k1_relat_1(sK5(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ),
    inference(resolution,[],[f72,f76])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',redefinition_k1_relset_1)).

fof(f176,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r2_hidden(X11,k1_relset_1(X9,X10,X8))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_xboole_0(X9) ) ),
    inference(resolution,[],[f71,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',t5_subset)).

fof(f378,plain,(
    ! [X19,X18] :
      ( r2_hidden(sK4(k1_xboole_0,X18,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18))),X19),k1_relat_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)))))
      | ~ v1_funct_1(X19)
      | ~ v1_funct_2(X19,k1_xboole_0,X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)))
      | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18))))
      | r1_partfun1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18))),X19) ) ),
    inference(subsumption_resolution,[],[f371,f76])).

fof(f371,plain,(
    ! [X19,X18] :
      ( r2_hidden(sK4(k1_xboole_0,X18,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18))),X19),k1_relat_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)))))
      | ~ m1_subset_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18))),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)))
      | ~ v1_funct_1(X19)
      | ~ v1_funct_2(X19,k1_xboole_0,X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18)))
      | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18))))
      | r1_partfun1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X18))),X19) ) ),
    inference(superposition,[],[f78,f187])).

fof(f2732,plain,
    ( ~ spl6_46
    | spl6_77
    | spl6_199
    | ~ spl6_248 ),
    inference(avatar_contradiction_clause,[],[f2731])).

fof(f2731,plain,
    ( $false
    | ~ spl6_46
    | ~ spl6_77
    | ~ spl6_199
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f2730,f599])).

fof(f2730,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_46
    | ~ spl6_199
    | ~ spl6_248 ),
    inference(forward_demodulation,[],[f2729,f2720])).

fof(f2720,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_relat_1(sK1)))
    | ~ spl6_248 ),
    inference(resolution,[],[f2715,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',t6_boole)).

fof(f2715,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_relat_1(sK1))))
    | ~ spl6_248 ),
    inference(avatar_component_clause,[],[f2714])).

fof(f2714,plain,
    ( spl6_248
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_248])])).

fof(f2729,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_relat_1(sK1))))
    | ~ spl6_46
    | ~ spl6_199
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f2724,f2122])).

fof(f2122,plain,
    ( k1_funct_1(sK1,sK5(k1_xboole_0)) != k1_funct_1(sK2,sK5(k1_xboole_0))
    | ~ spl6_199 ),
    inference(avatar_component_clause,[],[f2121])).

fof(f2121,plain,
    ( spl6_199
  <=> k1_funct_1(sK1,sK5(k1_xboole_0)) != k1_funct_1(sK2,sK5(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_199])])).

fof(f2724,plain,
    ( k1_funct_1(sK1,sK5(k1_xboole_0)) = k1_funct_1(sK2,sK5(k1_xboole_0))
    | v1_xboole_0(sK5(k1_zfmisc_1(k1_relat_1(sK1))))
    | ~ spl6_46
    | ~ spl6_248 ),
    inference(backward_demodulation,[],[f2720,f2501])).

fof(f2501,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_relat_1(sK1))))
    | k1_funct_1(sK1,sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1))))) = k1_funct_1(sK2,sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1)))))
    | ~ spl6_46 ),
    inference(resolution,[],[f1336,f291])).

fof(f2728,plain,
    ( spl6_77
    | ~ spl6_248 ),
    inference(avatar_contradiction_clause,[],[f2727])).

fof(f2727,plain,
    ( $false
    | ~ spl6_77
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f2723,f599])).

fof(f2723,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_248 ),
    inference(backward_demodulation,[],[f2720,f2715])).

fof(f2726,plain,
    ( spl6_247
    | ~ spl6_248 ),
    inference(avatar_contradiction_clause,[],[f2725])).

fof(f2725,plain,
    ( $false
    | ~ spl6_247
    | ~ spl6_248 ),
    inference(subsumption_resolution,[],[f2722,f76])).

fof(f2722,plain,
    ( ~ m1_subset_1(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl6_247
    | ~ spl6_248 ),
    inference(backward_demodulation,[],[f2720,f2706])).

fof(f2706,plain,
    ( ~ m1_subset_1(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1)))),k1_xboole_0)
    | ~ spl6_247 ),
    inference(avatar_component_clause,[],[f2705])).

fof(f2705,plain,
    ( spl6_247
  <=> ~ m1_subset_1(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_247])])).

fof(f2716,plain,
    ( spl6_246
    | spl6_248
    | ~ spl6_8
    | ~ spl6_38
    | spl6_43
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f2500,f514,f260,f250,f112,f2714,f2708])).

fof(f2500,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_relat_1(sK1))))
    | m1_subset_1(sK5(sK5(k1_zfmisc_1(k1_relat_1(sK1)))),k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_43
    | ~ spl6_66 ),
    inference(resolution,[],[f1336,f674])).

fof(f674,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK1))
        | m1_subset_1(X0,k1_xboole_0) )
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_43
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f665,f261])).

fof(f665,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_xboole_0)
        | v1_xboole_0(k1_relat_1(sK1))
        | ~ m1_subset_1(X0,k1_relat_1(sK1)) )
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(backward_demodulation,[],[f515,f519])).

fof(f2629,plain,
    ( spl6_136
    | spl6_76
    | ~ spl6_243
    | ~ spl6_66
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f2156,f1181,f514,f2441,f601,f1469])).

fof(f1469,plain,
    ( spl6_136
  <=> v1_xboole_0(sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).

fof(f2441,plain,
    ( spl6_243
  <=> ~ m1_subset_1(k1_xboole_0,sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_243])])).

fof(f2156,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK5(k1_relat_1(sK1)))
    | v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK5(k1_relat_1(sK1)))
    | ~ spl6_66
    | ~ spl6_102 ),
    inference(forward_demodulation,[],[f2155,f515])).

fof(f2155,plain,
    ( v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK5(k1_relat_1(sK1)))
    | ~ m1_subset_1(sK0,sK5(k1_relat_1(sK1)))
    | ~ spl6_66
    | ~ spl6_102 ),
    inference(forward_demodulation,[],[f1301,f515])).

fof(f1301,plain,
    ( v1_xboole_0(sK5(k1_relat_1(sK1)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK5(k1_relat_1(sK1)))
    | ~ spl6_102 ),
    inference(resolution,[],[f331,f1182])).

fof(f1182,plain,
    ( m1_subset_1(sK5(k1_relat_1(sK1)),sK0)
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f1181])).

fof(f2562,plain,
    ( ~ spl6_245
    | ~ spl6_66
    | spl6_139 ),
    inference(avatar_split_clause,[],[f1933,f1520,f514,f2560])).

fof(f2560,plain,
    ( spl6_245
  <=> ~ m1_subset_1(k1_xboole_0,sK5(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_245])])).

fof(f1520,plain,
    ( spl6_139
  <=> ~ m1_subset_1(sK0,sK5(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_139])])).

fof(f1933,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK5(k1_relat_1(sK2)))
    | ~ spl6_66
    | ~ spl6_139 ),
    inference(backward_demodulation,[],[f515,f1521])).

fof(f1521,plain,
    ( ~ m1_subset_1(sK0,sK5(k1_relat_1(sK2)))
    | ~ spl6_139 ),
    inference(avatar_component_clause,[],[f1520])).

fof(f2443,plain,
    ( ~ spl6_243
    | ~ spl6_66
    | spl6_135 ),
    inference(avatar_split_clause,[],[f2158,f1463,f514,f2441])).

fof(f1463,plain,
    ( spl6_135
  <=> ~ m1_subset_1(sK0,sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_135])])).

fof(f2158,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK5(k1_relat_1(sK1)))
    | ~ spl6_66
    | ~ spl6_135 ),
    inference(forward_demodulation,[],[f1464,f515])).

fof(f1464,plain,
    ( ~ m1_subset_1(sK0,sK5(k1_relat_1(sK1)))
    | ~ spl6_135 ),
    inference(avatar_component_clause,[],[f1463])).

fof(f2430,plain,
    ( spl6_240
    | spl6_42
    | ~ spl6_2
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f2144,f877,f91,f263,f2428])).

fof(f2428,plain,
    ( spl6_240
  <=> ! [X0] :
        ( k1_funct_1(sK1,sK5(k1_relat_1(sK1))) = k1_funct_1(X0,sK5(k1_relat_1(sK1)))
        | ~ v1_funct_1(X0)
        | ~ r1_partfun1(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_240])])).

fof(f263,plain,
    ( spl6_42
  <=> v1_xboole_0(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f2144,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_relat_1(sK1))
        | k1_funct_1(sK1,sK5(k1_relat_1(sK1))) = k1_funct_1(X0,sK5(k1_relat_1(sK1)))
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(sK1,X0)
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_88 ),
    inference(forward_demodulation,[],[f2143,f1999])).

fof(f1999,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_relat_1(sK1)
    | ~ spl6_88 ),
    inference(resolution,[],[f878,f72])).

fof(f2143,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,sK5(k1_relat_1(sK1))) = k1_funct_1(X0,sK5(k1_relat_1(sK1)))
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ r1_partfun1(sK1,X0)
        | v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_88 ),
    inference(forward_demodulation,[],[f2009,f1999])).

fof(f2009,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK1,sK5(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))) = k1_funct_1(X0,sK5(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)))
        | ~ r1_partfun1(sK1,X0)
        | v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f1995,f92])).

fof(f1995,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(sK1)
        | k1_funct_1(sK1,sK5(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))) = k1_funct_1(X0,sK5(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)))
        | ~ r1_partfun1(sK1,X0)
        | v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
        | ~ v1_funct_1(X0) )
    | ~ spl6_88 ),
    inference(resolution,[],[f878,f458])).

fof(f458,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9)))
      | ~ v1_funct_2(X8,k1_xboole_0,X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X9)))
      | ~ v1_funct_1(X10)
      | k1_funct_1(X8,sK5(k1_relset_1(k1_xboole_0,X9,X10))) = k1_funct_1(X10,sK5(k1_relset_1(k1_xboole_0,X9,X10)))
      | ~ r1_partfun1(X10,X8)
      | v1_xboole_0(k1_relset_1(k1_xboole_0,X9,X10))
      | ~ v1_funct_1(X8) ) ),
    inference(resolution,[],[f211,f76])).

fof(f2426,plain,
    ( ~ spl6_239
    | ~ spl6_66
    | spl6_167 ),
    inference(avatar_split_clause,[],[f1943,f1718,f514,f2424])).

fof(f2424,plain,
    ( spl6_239
  <=> ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_239])])).

fof(f1718,plain,
    ( spl6_167
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_167])])).

fof(f1943,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1)
    | ~ spl6_66
    | ~ spl6_167 ),
    inference(backward_demodulation,[],[f515,f1719])).

fof(f1719,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl6_167 ),
    inference(avatar_component_clause,[],[f1718])).

fof(f2411,plain,
    ( ~ spl6_237
    | ~ spl6_66
    | spl6_165 ),
    inference(avatar_split_clause,[],[f1942,f1701,f514,f2409])).

fof(f2409,plain,
    ( spl6_237
  <=> ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_237])])).

fof(f1701,plain,
    ( spl6_165
  <=> ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_165])])).

fof(f1942,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK2)
    | ~ spl6_66
    | ~ spl6_165 ),
    inference(backward_demodulation,[],[f515,f1702])).

fof(f1702,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ spl6_165 ),
    inference(avatar_component_clause,[],[f1701])).

fof(f2402,plain,
    ( spl6_42
    | spl6_234
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f2157,f514,f250,f112,f2400,f263])).

fof(f2400,plain,
    ( spl6_234
  <=> ! [X4] :
        ( m1_subset_1(X4,k1_xboole_0)
        | ~ m1_subset_1(X4,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_234])])).

fof(f2157,plain,
    ( ! [X4] :
        ( m1_subset_1(X4,k1_xboole_0)
        | v1_xboole_0(k1_relat_1(sK1))
        | ~ m1_subset_1(X4,k1_relat_1(sK1)) )
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f1800,f515])).

fof(f1800,plain,
    ( ! [X4] :
        ( v1_xboole_0(k1_relat_1(sK1))
        | ~ m1_subset_1(X4,k1_relat_1(sK1))
        | m1_subset_1(X4,sK0) )
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1799,f251])).

fof(f1799,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_relat_1(sK1))
        | m1_subset_1(X4,sK0)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK1)) )
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f1350,f113])).

fof(f1350,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_relat_1(sK1))
        | m1_subset_1(X4,sK0)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_38 ),
    inference(superposition,[],[f357,f251])).

fof(f357,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_relset_1(X1,X2,X0))
      | m1_subset_1(X3,X1)
      | v1_xboole_0(k1_relset_1(X1,X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f175,f68])).

fof(f2395,plain,
    ( spl6_232
    | ~ spl6_66
    | ~ spl6_122 ),
    inference(avatar_split_clause,[],[f1927,f1265,f514,f2393])).

fof(f2393,plain,
    ( spl6_232
  <=> m1_subset_1(sK5(k1_relat_1(sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_232])])).

fof(f1265,plain,
    ( spl6_122
  <=> m1_subset_1(sK5(k1_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).

fof(f1927,plain,
    ( m1_subset_1(sK5(k1_relat_1(sK2)),k1_xboole_0)
    | ~ spl6_66
    | ~ spl6_122 ),
    inference(backward_demodulation,[],[f515,f1266])).

fof(f1266,plain,
    ( m1_subset_1(sK5(k1_relat_1(sK2)),sK0)
    | ~ spl6_122 ),
    inference(avatar_component_clause,[],[f1265])).

fof(f2385,plain,
    ( ~ spl6_231
    | ~ spl6_66
    | spl6_171 ),
    inference(avatar_split_clause,[],[f1945,f1763,f514,f2383])).

fof(f2383,plain,
    ( spl6_231
  <=> ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_231])])).

fof(f1763,plain,
    ( spl6_171
  <=> ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_171])])).

fof(f1945,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0,k1_xboole_0)
    | ~ spl6_66
    | ~ spl6_171 ),
    inference(backward_demodulation,[],[f515,f1764])).

fof(f1764,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK0,sK0)
    | ~ spl6_171 ),
    inference(avatar_component_clause,[],[f1763])).

fof(f2376,plain,
    ( ~ spl6_229
    | ~ spl6_66
    | spl6_179 ),
    inference(avatar_split_clause,[],[f1947,f1782,f514,f2374])).

fof(f2374,plain,
    ( spl6_229
  <=> ~ r1_partfun1(sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_229])])).

fof(f1782,plain,
    ( spl6_179
  <=> ~ r1_partfun1(sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_179])])).

fof(f1947,plain,
    ( ~ r1_partfun1(sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))
    | ~ spl6_66
    | ~ spl6_179 ),
    inference(backward_demodulation,[],[f515,f1783])).

fof(f1783,plain,
    ( ~ r1_partfun1(sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl6_179 ),
    inference(avatar_component_clause,[],[f1782])).

fof(f2369,plain,
    ( ~ spl6_227
    | ~ spl6_66
    | spl6_175 ),
    inference(avatar_split_clause,[],[f1946,f1772,f514,f2367])).

fof(f2367,plain,
    ( spl6_227
  <=> ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_227])])).

fof(f1772,plain,
    ( spl6_175
  <=> ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_175])])).

fof(f1946,plain,
    ( ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))
    | ~ spl6_66
    | ~ spl6_175 ),
    inference(backward_demodulation,[],[f515,f1773])).

fof(f1773,plain,
    ( ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl6_175 ),
    inference(avatar_component_clause,[],[f1772])).

fof(f2361,plain,
    ( ~ spl6_225
    | ~ spl6_66
    | spl6_163 ),
    inference(avatar_split_clause,[],[f1941,f1694,f514,f2359])).

fof(f2359,plain,
    ( spl6_225
  <=> ~ v1_xboole_0(k1_relat_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_225])])).

fof(f1694,plain,
    ( spl6_163
  <=> ~ v1_xboole_0(k1_relat_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_163])])).

fof(f1941,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))))
    | ~ spl6_66
    | ~ spl6_163 ),
    inference(backward_demodulation,[],[f515,f1695])).

fof(f1695,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | ~ spl6_163 ),
    inference(avatar_component_clause,[],[f1694])).

fof(f2354,plain,
    ( ~ spl6_223
    | ~ spl6_66
    | spl6_161 ),
    inference(avatar_split_clause,[],[f1940,f1685,f514,f2352])).

fof(f2352,plain,
    ( spl6_223
  <=> ~ r1_partfun1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_223])])).

fof(f1685,plain,
    ( spl6_161
  <=> ~ r1_partfun1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_161])])).

fof(f1940,plain,
    ( ~ r1_partfun1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),sK2)
    | ~ spl6_66
    | ~ spl6_161 ),
    inference(backward_demodulation,[],[f515,f1686])).

fof(f1686,plain,
    ( ~ r1_partfun1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK2)
    | ~ spl6_161 ),
    inference(avatar_component_clause,[],[f1685])).

fof(f2344,plain,
    ( spl6_220
    | ~ spl6_66
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f2160,f1181,f514,f2342])).

fof(f2342,plain,
    ( spl6_220
  <=> m1_subset_1(sK5(k1_relat_1(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_220])])).

fof(f2160,plain,
    ( m1_subset_1(sK5(k1_relat_1(sK1)),k1_xboole_0)
    | ~ spl6_66
    | ~ spl6_102 ),
    inference(forward_demodulation,[],[f1182,f515])).

fof(f2337,plain,
    ( ~ spl6_219
    | ~ spl6_66
    | spl6_151 ),
    inference(avatar_split_clause,[],[f1937,f1656,f514,f2335])).

fof(f2335,plain,
    ( spl6_219
  <=> ~ r2_hidden(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_219])])).

fof(f1656,plain,
    ( spl6_151
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_151])])).

fof(f1937,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK2)
    | ~ spl6_66
    | ~ spl6_151 ),
    inference(backward_demodulation,[],[f515,f1657])).

fof(f1657,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ spl6_151 ),
    inference(avatar_component_clause,[],[f1656])).

fof(f2330,plain,
    ( ~ spl6_77
    | spl6_60
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f2114,f1164,f490,f598])).

fof(f490,plain,
    ( spl6_60
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f1164,plain,
    ( spl6_100
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f2114,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl6_100 ),
    inference(resolution,[],[f1165,f65])).

fof(f1165,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f1164])).

fof(f2329,plain,
    ( ~ spl6_217
    | ~ spl6_66
    | spl6_159 ),
    inference(avatar_split_clause,[],[f1939,f1682,f514,f2327])).

fof(f2327,plain,
    ( spl6_217
  <=> ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_217])])).

fof(f1682,plain,
    ( spl6_159
  <=> ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_159])])).

fof(f1939,plain,
    ( ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))
    | ~ spl6_66
    | ~ spl6_159 ),
    inference(backward_demodulation,[],[f515,f1683])).

fof(f1683,plain,
    ( ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl6_159 ),
    inference(avatar_component_clause,[],[f1682])).

fof(f2322,plain,
    ( ~ spl6_215
    | ~ spl6_66
    | spl6_153 ),
    inference(avatar_split_clause,[],[f1938,f1663,f514,f2320])).

fof(f2320,plain,
    ( spl6_215
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_215])])).

fof(f1663,plain,
    ( spl6_153
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_153])])).

fof(f1938,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK2)
    | ~ spl6_66
    | ~ spl6_153 ),
    inference(backward_demodulation,[],[f515,f1664])).

fof(f1664,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK2)
    | ~ spl6_153 ),
    inference(avatar_component_clause,[],[f1663])).

fof(f2315,plain,
    ( ~ spl6_213
    | ~ spl6_66
    | spl6_143 ),
    inference(avatar_split_clause,[],[f1934,f1605,f514,f2313])).

fof(f2313,plain,
    ( spl6_213
  <=> ~ r2_hidden(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_213])])).

fof(f1605,plain,
    ( spl6_143
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_143])])).

fof(f1934,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK1)
    | ~ spl6_66
    | ~ spl6_143 ),
    inference(backward_demodulation,[],[f515,f1606])).

fof(f1606,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl6_143 ),
    inference(avatar_component_clause,[],[f1605])).

fof(f2308,plain,
    ( ~ spl6_211
    | ~ spl6_66
    | spl6_145 ),
    inference(avatar_split_clause,[],[f1935,f1637,f514,f2306])).

fof(f2306,plain,
    ( spl6_211
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_211])])).

fof(f1637,plain,
    ( spl6_145
  <=> ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_145])])).

fof(f1935,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),sK1)
    | ~ spl6_66
    | ~ spl6_145 ),
    inference(backward_demodulation,[],[f515,f1638])).

fof(f1638,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1)
    | ~ spl6_145 ),
    inference(avatar_component_clause,[],[f1637])).

fof(f2262,plain,
    ( ~ spl6_209
    | ~ spl6_66
    | spl6_133 ),
    inference(avatar_split_clause,[],[f2159,f1403,f514,f2260])).

fof(f2260,plain,
    ( spl6_209
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_209])])).

fof(f1403,plain,
    ( spl6_133
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_133])])).

fof(f2159,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_relat_1(sK1))
    | ~ spl6_66
    | ~ spl6_133 ),
    inference(forward_demodulation,[],[f1404,f515])).

fof(f1404,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK1))
    | ~ spl6_133 ),
    inference(avatar_component_clause,[],[f1403])).

fof(f2251,plain,
    ( ~ spl6_207
    | ~ spl6_66
    | spl6_147 ),
    inference(avatar_split_clause,[],[f1936,f1640,f514,f2249])).

fof(f2249,plain,
    ( spl6_207
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_207])])).

fof(f1640,plain,
    ( spl6_147
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_147])])).

fof(f1936,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_66
    | ~ spl6_147 ),
    inference(backward_demodulation,[],[f515,f1641])).

fof(f1641,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_147 ),
    inference(avatar_component_clause,[],[f1640])).

fof(f2238,plain,
    ( ~ spl6_205
    | ~ spl6_66
    | spl6_127 ),
    inference(avatar_split_clause,[],[f1930,f1325,f514,f2236])).

fof(f2236,plain,
    ( spl6_205
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_205])])).

fof(f1325,plain,
    ( spl6_127
  <=> ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_127])])).

fof(f1930,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_relat_1(sK2))
    | ~ spl6_66
    | ~ spl6_127 ),
    inference(backward_demodulation,[],[f515,f1326])).

fof(f1326,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK2))
    | ~ spl6_127 ),
    inference(avatar_component_clause,[],[f1325])).

fof(f2231,plain,
    ( spl6_62
    | ~ spl6_77
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f2145,f514,f250,f112,f598,f501])).

fof(f2145,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X4,k1_relat_1(sK1)) )
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f1864,f515])).

fof(f1864,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | ~ v1_xboole_0(sK0) )
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f615,f113])).

fof(f615,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_xboole_0(sK0) )
    | ~ spl6_38 ),
    inference(superposition,[],[f176,f251])).

fof(f2227,plain,
    ( spl6_202
    | ~ spl6_52
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f655,f514,f339,f2225])).

fof(f2225,plain,
    ( spl6_202
  <=> m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_202])])).

fof(f339,plain,
    ( spl6_52
  <=> m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f655,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_52
    | ~ spl6_66 ),
    inference(backward_demodulation,[],[f515,f340])).

fof(f340,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f339])).

fof(f2220,plain,
    ( spl6_42
    | spl6_46
    | ~ spl6_18
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f609,f250,f143,f290,f263])).

fof(f143,plain,
    ( spl6_18
  <=> ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))
        | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f609,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
        | v1_xboole_0(k1_relat_1(sK1))
        | ~ m1_subset_1(X0,k1_relat_1(sK1)) )
    | ~ spl6_18
    | ~ spl6_38 ),
    inference(resolution,[],[f313,f68])).

fof(f313,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK1))
        | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) )
    | ~ spl6_18
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f144,f251])).

fof(f144,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))
        | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f2185,plain,
    ( spl6_98
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f1999,f877,f1058])).

fof(f2183,plain,
    ( ~ spl6_43
    | ~ spl6_0
    | ~ spl6_2
    | spl6_11
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f2174,f877,f771,f679,f119,f91,f84,f260])).

fof(f2174,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88 ),
    inference(forward_demodulation,[],[f2139,f1999])).

fof(f2139,plain,
    ( ~ v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f2138,f120])).

fof(f2138,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88 ),
    inference(subsumption_resolution,[],[f2133,f92])).

fof(f2133,plain,
    ( ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,sK1))
    | ~ spl6_0
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88 ),
    inference(resolution,[],[f1994,f878])).

fof(f1994,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X3)
        | r1_partfun1(X3,sK2)
        | ~ v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,X3)) )
    | ~ spl6_0
    | ~ spl6_80
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f1993,f680])).

fof(f1993,plain,
    ( ! [X3] :
        ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X3)
        | r1_partfun1(X3,sK2)
        | ~ v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,X3)) )
    | ~ spl6_0
    | ~ spl6_84 ),
    inference(subsumption_resolution,[],[f1974,f85])).

fof(f1974,plain,
    ( ! [X3] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X3)
        | r1_partfun1(X3,sK2)
        | ~ v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,X3)) )
    | ~ spl6_84 ),
    inference(resolution,[],[f772,f207])).

fof(f207,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X7)))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,k1_xboole_0,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X7)))
      | ~ v1_funct_1(X6)
      | r1_partfun1(X6,X8)
      | ~ v1_xboole_0(k1_relset_1(k1_xboole_0,X7,X6)) ) ),
    inference(resolution,[],[f78,f67])).

fof(f2142,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_11
    | ~ spl6_76
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_188 ),
    inference(avatar_contradiction_clause,[],[f2141])).

fof(f2141,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_76
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_188 ),
    inference(subsumption_resolution,[],[f2140,f602])).

fof(f602,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f601])).

fof(f2140,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_80
    | ~ spl6_84
    | ~ spl6_88
    | ~ spl6_188 ),
    inference(forward_demodulation,[],[f2139,f2036])).

fof(f2036,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0
    | ~ spl6_188 ),
    inference(avatar_component_clause,[],[f2035])).

fof(f2035,plain,
    ( spl6_188
  <=> k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_188])])).

fof(f2130,plain,
    ( ~ spl6_201
    | ~ spl6_38
    | ~ spl6_42
    | spl6_137 ),
    inference(avatar_split_clause,[],[f1830,f1466,f263,f250,f2128])).

fof(f2128,plain,
    ( spl6_201
  <=> ~ v1_xboole_0(sK5(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_201])])).

fof(f1466,plain,
    ( spl6_137
  <=> ~ v1_xboole_0(sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_137])])).

fof(f1830,plain,
    ( ~ v1_xboole_0(sK5(k1_xboole_0))
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_137 ),
    inference(backward_demodulation,[],[f1807,f1467])).

fof(f1467,plain,
    ( ~ v1_xboole_0(sK5(k1_relat_1(sK1)))
    | ~ spl6_137 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f1807,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl6_38
    | ~ spl6_42 ),
    inference(backward_demodulation,[],[f573,f251])).

fof(f573,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_xboole_0
    | ~ spl6_38
    | ~ spl6_42 ),
    inference(backward_demodulation,[],[f571,f251])).

fof(f571,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl6_42 ),
    inference(resolution,[],[f264,f63])).

fof(f264,plain,
    ( v1_xboole_0(k1_relat_1(sK1))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f263])).

fof(f2123,plain,
    ( ~ spl6_199
    | ~ spl6_42
    | spl6_75 ),
    inference(avatar_split_clause,[],[f587,f563,f263,f2121])).

fof(f563,plain,
    ( spl6_75
  <=> k1_funct_1(sK1,sK5(k1_relat_1(sK1))) != k1_funct_1(sK2,sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f587,plain,
    ( k1_funct_1(sK1,sK5(k1_xboole_0)) != k1_funct_1(sK2,sK5(k1_xboole_0))
    | ~ spl6_42
    | ~ spl6_75 ),
    inference(backward_demodulation,[],[f571,f564])).

fof(f564,plain,
    ( k1_funct_1(sK1,sK5(k1_relat_1(sK1))) != k1_funct_1(sK2,sK5(k1_relat_1(sK1)))
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f563])).

fof(f2109,plain,
    ( spl6_196
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_52
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f1910,f514,f339,f263,f250,f2107])).

fof(f2107,plain,
    ( spl6_196
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_196])])).

fof(f1910,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_52
    | ~ spl6_66 ),
    inference(forward_demodulation,[],[f655,f1807])).

fof(f2102,plain,
    ( ~ spl6_195
    | ~ spl6_66
    | spl6_129 ),
    inference(avatar_split_clause,[],[f1931,f1328,f514,f2100])).

fof(f2100,plain,
    ( spl6_195
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_195])])).

fof(f1328,plain,
    ( spl6_129
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).

fof(f1931,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_66
    | ~ spl6_129 ),
    inference(backward_demodulation,[],[f515,f1329])).

fof(f1329,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl6_129 ),
    inference(avatar_component_clause,[],[f1328])).

fof(f2095,plain,
    ( ~ spl6_193
    | ~ spl6_66
    | spl6_73 ),
    inference(avatar_split_clause,[],[f668,f544,f514,f2093])).

fof(f2093,plain,
    ( spl6_193
  <=> ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_193])])).

fof(f544,plain,
    ( spl6_73
  <=> ~ v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f668,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl6_66
    | ~ spl6_73 ),
    inference(backward_demodulation,[],[f515,f545])).

fof(f545,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f544])).

fof(f2044,plain,
    ( ~ spl6_191
    | ~ spl6_42
    | spl6_55 ),
    inference(avatar_split_clause,[],[f582,f399,f263,f2042])).

fof(f2042,plain,
    ( spl6_191
  <=> ~ m1_subset_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_191])])).

fof(f399,plain,
    ( spl6_55
  <=> ~ m1_subset_1(k1_relat_1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f582,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK3)
    | ~ spl6_42
    | ~ spl6_55 ),
    inference(backward_demodulation,[],[f571,f400])).

fof(f400,plain,
    ( ~ m1_subset_1(k1_relat_1(sK1),sK3)
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f399])).

fof(f2037,plain,
    ( spl6_188
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f1909,f1058,f263,f250,f2035])).

fof(f1909,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_xboole_0
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_98 ),
    inference(forward_demodulation,[],[f1059,f1807])).

fof(f2030,plain,
    ( spl6_186
    | ~ spl6_38
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f1807,f263,f250,f2028])).

fof(f2028,plain,
    ( spl6_186
  <=> k1_xboole_0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_186])])).

fof(f2022,plain,
    ( ~ spl6_185
    | ~ spl6_42
    | spl6_51 ),
    inference(avatar_split_clause,[],[f579,f325,f263,f2020])).

fof(f2020,plain,
    ( spl6_185
  <=> ~ r2_hidden(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_185])])).

fof(f325,plain,
    ( spl6_51
  <=> ~ r2_hidden(k1_relat_1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f579,plain,
    ( ~ r2_hidden(k1_xboole_0,sK3)
    | ~ spl6_42
    | ~ spl6_51 ),
    inference(backward_demodulation,[],[f571,f326])).

fof(f326,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK3)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f325])).

fof(f1971,plain,
    ( ~ spl6_183
    | spl6_29
    | ~ spl6_38
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f1808,f263,f250,f198,f1969])).

fof(f198,plain,
    ( spl6_29
  <=> ~ r2_hidden(sK3,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f1808,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | ~ spl6_29
    | ~ spl6_38
    | ~ spl6_42 ),
    inference(backward_demodulation,[],[f1807,f199])).

fof(f199,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f198])).

fof(f1846,plain,
    ( ~ spl6_2
    | ~ spl6_8
    | spl6_11
    | ~ spl6_18
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_78 ),
    inference(avatar_contradiction_clause,[],[f1845])).

fof(f1845,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_18
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_78 ),
    inference(global_subsumption,[],[f264,f1174])).

fof(f1174,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_78 ),
    inference(forward_demodulation,[],[f1173,f251])).

fof(f1173,plain,
    ( ~ v1_xboole_0(k1_relset_1(sK0,sK0,sK1))
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f1172,f92])).

fof(f1172,plain,
    ( ~ v1_xboole_0(k1_relset_1(sK0,sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f1169,f120])).

fof(f1169,plain,
    ( ~ v1_xboole_0(k1_relset_1(sK0,sK0,sK1))
    | r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ spl6_8
    | ~ spl6_78 ),
    inference(resolution,[],[f630,f113])).

fof(f630,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X0))
        | r1_partfun1(X0,sK2)
        | ~ v1_funct_1(X0) )
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f629])).

fof(f1844,plain,
    ( ~ spl6_2
    | ~ spl6_8
    | spl6_11
    | ~ spl6_38
    | ~ spl6_42
    | spl6_67
    | ~ spl6_78
    | ~ spl6_108 ),
    inference(avatar_contradiction_clause,[],[f1843])).

fof(f1843,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_67
    | ~ spl6_78
    | ~ spl6_108 ),
    inference(global_subsumption,[],[f264,f1174])).

fof(f1836,plain,
    ( ~ spl6_2
    | ~ spl6_8
    | spl6_11
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_76
    | ~ spl6_78 ),
    inference(avatar_contradiction_clause,[],[f1835])).

fof(f1835,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_76
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f1817,f602])).

fof(f1817,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_38
    | ~ spl6_42
    | ~ spl6_78 ),
    inference(backward_demodulation,[],[f1807,f1174])).

fof(f1798,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | spl6_11
    | spl6_67
    | ~ spl6_168 ),
    inference(avatar_contradiction_clause,[],[f1797])).

fof(f1797,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_67
    | ~ spl6_168 ),
    inference(subsumption_resolution,[],[f1796,f120])).

fof(f1796,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_67
    | ~ spl6_168 ),
    inference(subsumption_resolution,[],[f1795,f92])).

fof(f1795,plain,
    ( ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_67
    | ~ spl6_168 ),
    inference(subsumption_resolution,[],[f1794,f512])).

fof(f512,plain,
    ( k1_xboole_0 != sK0
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f511])).

fof(f511,plain,
    ( spl6_67
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f1794,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_168 ),
    inference(subsumption_resolution,[],[f1793,f106])).

fof(f1793,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_168 ),
    inference(subsumption_resolution,[],[f1792,f99])).

fof(f1792,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_0
    | ~ spl6_8
    | ~ spl6_168 ),
    inference(subsumption_resolution,[],[f1791,f85])).

fof(f1791,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_8
    | ~ spl6_168 ),
    inference(subsumption_resolution,[],[f1790,f113])).

fof(f1790,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_168 ),
    inference(trivial_inequality_removal,[],[f1789])).

fof(f1789,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) != k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | r1_partfun1(sK1,sK2)
    | ~ spl6_168 ),
    inference(superposition,[],[f58,f1747])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK4(X0,X1,X2,X3)) != k1_funct_1(X3,sK4(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X2)
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1788,plain,
    ( ~ spl6_171
    | ~ spl6_159
    | spl6_180
    | ~ spl6_179
    | ~ spl6_118 ),
    inference(avatar_split_clause,[],[f1249,f1243,f1782,f1786,f1682,f1763])).

fof(f1786,plain,
    ( spl6_180
  <=> ! [X5] :
        ( k1_funct_1(sK1,X5) = k1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),X5)
        | ~ r2_hidden(X5,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_180])])).

fof(f1249,plain,
    ( ! [X5] :
        ( ~ r1_partfun1(sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
        | k1_funct_1(sK1,X5) = k1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),X5)
        | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
        | ~ r2_hidden(X5,k1_relat_1(sK1))
        | ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK0,sK0) )
    | ~ spl6_118 ),
    inference(resolution,[],[f1244,f76])).

fof(f1784,plain,
    ( ~ spl6_171
    | ~ spl6_159
    | spl6_176
    | ~ spl6_179
    | ~ spl6_116 ),
    inference(avatar_split_clause,[],[f1241,f1235,f1782,f1776,f1682,f1763])).

fof(f1776,plain,
    ( spl6_176
  <=> ! [X5] :
        ( k1_funct_1(sK1,X5) = k1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),X5)
        | ~ m1_subset_1(X5,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_176])])).

fof(f1241,plain,
    ( ! [X5] :
        ( ~ r1_partfun1(sK1,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
        | k1_funct_1(sK1,X5) = k1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),X5)
        | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
        | ~ m1_subset_1(X5,k1_relat_1(sK1))
        | ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK0,sK0) )
    | ~ spl6_116 ),
    inference(resolution,[],[f1236,f76])).

fof(f1236,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK1,X8)
        | k1_funct_1(sK1,X7) = k1_funct_1(X8,X7)
        | ~ v1_funct_1(X8)
        | ~ m1_subset_1(X7,k1_relat_1(sK1))
        | ~ v1_funct_2(X8,sK0,sK0) )
    | ~ spl6_116 ),
    inference(avatar_component_clause,[],[f1235])).

fof(f1774,plain,
    ( ~ spl6_171
    | ~ spl6_159
    | spl6_172
    | ~ spl6_175
    | ~ spl6_114 ),
    inference(avatar_split_clause,[],[f1233,f1227,f1772,f1766,f1682,f1763])).

fof(f1766,plain,
    ( spl6_172
  <=> ! [X5] :
        ( k1_funct_1(sK2,X5) = k1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),X5)
        | ~ r2_hidden(X5,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_172])])).

fof(f1227,plain,
    ( spl6_114
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r1_partfun1(sK2,X1)
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X1,sK0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).

fof(f1233,plain,
    ( ! [X5] :
        ( ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
        | k1_funct_1(sK2,X5) = k1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),X5)
        | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
        | ~ r2_hidden(X5,k1_relat_1(sK2))
        | ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK0,sK0) )
    | ~ spl6_114 ),
    inference(resolution,[],[f1228,f76])).

fof(f1228,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(sK2,X1)
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_2(X1,sK0,sK0) )
    | ~ spl6_114 ),
    inference(avatar_component_clause,[],[f1227])).

fof(f1748,plain,
    ( spl6_168
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6
    | spl6_11
    | ~ spl6_46
    | ~ spl6_104 ),
    inference(avatar_split_clause,[],[f1735,f1190,f290,f119,f105,f98,f84,f1746])).

fof(f1190,plain,
    ( spl6_104
  <=> ! [X6] :
        ( m1_subset_1(sK4(sK0,sK0,sK1,X6),k1_relat_1(sK1))
        | r1_partfun1(sK1,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X6,sK0,sK0)
        | ~ v1_funct_1(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f1735,plain,
    ( k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_46
    | ~ spl6_104 ),
    inference(subsumption_resolution,[],[f1734,f85])).

fof(f1734,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_46
    | ~ spl6_104 ),
    inference(subsumption_resolution,[],[f1733,f99])).

fof(f1733,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_46
    | ~ spl6_104 ),
    inference(subsumption_resolution,[],[f1730,f120])).

fof(f1730,plain,
    ( r1_partfun1(sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | k1_funct_1(sK1,sK4(sK0,sK0,sK1,sK2)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,sK2))
    | ~ spl6_6
    | ~ spl6_46
    | ~ spl6_104 ),
    inference(resolution,[],[f1193,f106])).

fof(f1193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r1_partfun1(sK1,X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK1,sK4(sK0,sK0,sK1,X0)) = k1_funct_1(sK2,sK4(sK0,sK0,sK1,X0)) )
    | ~ spl6_46
    | ~ spl6_104 ),
    inference(resolution,[],[f1191,f291])).

fof(f1191,plain,
    ( ! [X6] :
        ( m1_subset_1(sK4(sK0,sK0,sK1,X6),k1_relat_1(sK1))
        | r1_partfun1(sK1,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X6,sK0,sK0)
        | ~ v1_funct_1(X6) )
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f1190])).

fof(f1720,plain,
    ( ~ spl6_167
    | spl6_148
    | spl6_143 ),
    inference(avatar_split_clause,[],[f1632,f1605,f1649,f1718])).

fof(f1649,plain,
    ( spl6_148
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).

fof(f1632,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl6_143 ),
    inference(resolution,[],[f1606,f68])).

fof(f1703,plain,
    ( ~ spl6_165
    | spl6_151
    | spl6_155 ),
    inference(avatar_split_clause,[],[f1673,f1666,f1656,f1701])).

fof(f1666,plain,
    ( spl6_155
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_155])])).

fof(f1673,plain,
    ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ spl6_151
    | ~ spl6_155 ),
    inference(subsumption_resolution,[],[f1672,f1667])).

fof(f1667,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl6_155 ),
    inference(avatar_component_clause,[],[f1666])).

fof(f1672,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ spl6_151 ),
    inference(resolution,[],[f1657,f68])).

fof(f1696,plain,
    ( ~ spl6_159
    | spl6_160
    | ~ spl6_163
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f1175,f629,f1694,f1688,f1682])).

fof(f1688,plain,
    ( spl6_160
  <=> r1_partfun1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_160])])).

fof(f1175,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | r1_partfun1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK2)
    | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl6_78 ),
    inference(forward_demodulation,[],[f1171,f187])).

fof(f1171,plain,
    ( ~ v1_xboole_0(k1_relset_1(sK0,sK0,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))))
    | r1_partfun1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK2)
    | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))
    | ~ spl6_78 ),
    inference(resolution,[],[f630,f76])).

fof(f1677,plain,
    ( ~ spl6_111
    | spl6_156
    | ~ spl6_82 ),
    inference(avatar_split_clause,[],[f833,f731,f1675,f1217])).

fof(f1675,plain,
    ( spl6_156
  <=> ! [X4] :
        ( r1_partfun1(sK2,X4)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,sK0,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_156])])).

fof(f833,plain,
    ( ! [X4] :
        ( r1_partfun1(sK2,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X4,sK0,sK0)
        | ~ v1_funct_1(X4)
        | ~ v1_xboole_0(k1_relat_1(sK2)) )
    | ~ spl6_82 ),
    inference(resolution,[],[f732,f67])).

fof(f732,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK2,X2),k1_relat_1(sK2))
        | r1_partfun1(sK2,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ v1_funct_1(X2) )
    | ~ spl6_82 ),
    inference(avatar_component_clause,[],[f731])).

fof(f1671,plain,
    ( ~ spl6_153
    | spl6_146
    | spl6_154
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f1296,f105,f1669,f1643,f1663])).

fof(f1643,plain,
    ( spl6_146
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_146])])).

fof(f1669,plain,
    ( spl6_154
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_154])])).

fof(f1296,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f331,f106])).

fof(f1658,plain,
    ( ~ spl6_151
    | ~ spl6_6
    | spl6_31 ),
    inference(avatar_split_clause,[],[f1631,f222,f105,f1656])).

fof(f222,plain,
    ( spl6_31
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f1631,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f1630,f223])).

fof(f223,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f222])).

fof(f1630,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(duplicate_literal_removal,[],[f1629])).

fof(f1629,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK2)
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(resolution,[],[f1303,f157])).

fof(f157,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(sK0,sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_6 ),
    inference(resolution,[],[f66,f106])).

fof(f1303,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X2)
        | v1_xboole_0(X2)
        | ~ r2_hidden(X2,sK2) )
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f1290,f223])).

fof(f1290,plain,
    ( ! [X2] :
        ( v1_xboole_0(X2)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X2)
        | ~ r2_hidden(X2,sK2) )
    | ~ spl6_6 ),
    inference(resolution,[],[f331,f157])).

fof(f1651,plain,
    ( ~ spl6_145
    | spl6_146
    | spl6_148
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f1295,f112,f1649,f1643,f1637])).

fof(f1295,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)),sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f331,f113])).

fof(f1607,plain,
    ( ~ spl6_143
    | ~ spl6_8
    | spl6_31 ),
    inference(avatar_split_clause,[],[f1593,f222,f112,f1605])).

fof(f1593,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl6_8
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f1592,f223])).

fof(f1592,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl6_8
    | ~ spl6_31 ),
    inference(duplicate_literal_removal,[],[f1590])).

fof(f1590,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK0))
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK0),sK1)
    | ~ spl6_8
    | ~ spl6_31 ),
    inference(resolution,[],[f1302,f158])).

fof(f158,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k2_zfmisc_1(sK0,sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_8 ),
    inference(resolution,[],[f66,f113])).

fof(f1302,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X1)
        | v1_xboole_0(X1)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_8
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f1289,f223])).

fof(f1289,plain,
    ( ! [X1] :
        ( v1_xboole_0(X1)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK0))
        | ~ m1_subset_1(k2_zfmisc_1(sK0,sK0),X1)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_8 ),
    inference(resolution,[],[f331,f158])).

fof(f1528,plain,
    ( ~ spl6_139
    | spl6_140
    | spl6_59
    | ~ spl6_122 ),
    inference(avatar_split_clause,[],[f1308,f1265,f487,f1526,f1520])).

fof(f1526,plain,
    ( spl6_140
  <=> v1_xboole_0(sK5(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_140])])).

fof(f1308,plain,
    ( v1_xboole_0(sK5(k1_relat_1(sK2)))
    | ~ m1_subset_1(sK0,sK5(k1_relat_1(sK2)))
    | ~ spl6_59
    | ~ spl6_122 ),
    inference(subsumption_resolution,[],[f1307,f488])).

fof(f1307,plain,
    ( v1_xboole_0(sK5(k1_relat_1(sK2)))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK0,sK5(k1_relat_1(sK2)))
    | ~ spl6_122 ),
    inference(resolution,[],[f1266,f331])).

fof(f1471,plain,
    ( ~ spl6_135
    | spl6_136
    | spl6_59
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f1306,f1181,f487,f1469,f1463])).

fof(f1306,plain,
    ( v1_xboole_0(sK5(k1_relat_1(sK1)))
    | ~ m1_subset_1(sK0,sK5(k1_relat_1(sK1)))
    | ~ spl6_59
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f1301,f488])).

fof(f1405,plain,
    ( ~ spl6_133
    | spl6_128
    | spl6_43
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f1305,f339,f260,f1331,f1403])).

fof(f1331,plain,
    ( spl6_128
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).

fof(f1305,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK1))
    | ~ spl6_43
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f1293,f261])).

fof(f1293,plain,
    ( v1_xboole_0(k1_relat_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK1))
    | ~ spl6_52 ),
    inference(resolution,[],[f331,f340])).

fof(f1396,plain,
    ( ~ spl6_77
    | spl6_130 ),
    inference(avatar_split_clause,[],[f349,f1394,f598])).

fof(f1394,plain,
    ( spl6_130
  <=> ! [X5,X4,X6] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
        | r1_partfun1(X4,X6)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,k1_xboole_0,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).

fof(f349,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k1_xboole_0,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X4)
      | r1_partfun1(X4,X6) ) ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k1_xboole_0,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X4)
      | r1_partfun1(X4,X6) ) ),
    inference(resolution,[],[f176,f78])).

fof(f1333,plain,
    ( ~ spl6_127
    | spl6_128
    | ~ spl6_44
    | spl6_111 ),
    inference(avatar_split_clause,[],[f1304,f1217,f286,f1331,f1325])).

fof(f286,plain,
    ( spl6_44
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f1304,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK2))
    | ~ spl6_44
    | ~ spl6_111 ),
    inference(subsumption_resolution,[],[f1292,f1218])).

fof(f1292,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_zfmisc_1(sK0),k1_relat_1(sK2))
    | ~ spl6_44 ),
    inference(resolution,[],[f331,f287])).

fof(f287,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f286])).

fof(f1313,plain,
    ( spl6_66
    | spl6_124
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f498,f105,f98,f84,f1311,f514])).

fof(f1311,plain,
    ( spl6_124
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | r1_partfun1(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r1_partfun1(X1,X0)
        | k1_funct_1(X0,sK4(sK0,sK0,X1,sK2)) = k1_funct_1(X1,sK4(sK0,sK0,X1,sK2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X0,sK0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).

fof(f498,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X1)
        | k1_funct_1(X0,sK4(sK0,sK0,X1,sK2)) = k1_funct_1(X1,sK4(sK0,sK0,X1,sK2))
        | ~ r1_partfun1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r1_partfun1(X1,sK2) )
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f497,f99])).

fof(f497,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X1)
        | k1_funct_1(X0,sK4(sK0,sK0,X1,sK2)) = k1_funct_1(X1,sK4(sK0,sK0,X1,sK2))
        | ~ r1_partfun1(X1,X0)
        | ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r1_partfun1(X1,sK2) )
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f493,f85])).

fof(f493,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X1)
        | k1_funct_1(X0,sK4(sK0,sK0,X1,sK2)) = k1_funct_1(X1,sK4(sK0,sK0,X1,sK2))
        | ~ r1_partfun1(X1,X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | r1_partfun1(X1,sK2) )
    | ~ spl6_6 ),
    inference(resolution,[],[f231,f106])).

fof(f231,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,X10,X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k1_xboole_0 = X11
      | ~ v1_funct_1(X9)
      | k1_funct_1(X9,sK4(X10,X11,X9,X13)) = k1_funct_1(X12,sK4(X10,X11,X9,X13))
      | ~ r1_partfun1(X9,X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,X10,X11)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | r1_partfun1(X9,X13) ) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,X10,X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k1_xboole_0 = X11
      | ~ v1_funct_1(X9)
      | k1_funct_1(X9,sK4(X10,X11,X9,X13)) = k1_funct_1(X12,sK4(X10,X11,X9,X13))
      | ~ r1_partfun1(X9,X12)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,X10,X11)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k1_xboole_0 = X11
      | ~ v1_funct_1(X9)
      | r1_partfun1(X9,X13) ) ),
    inference(resolution,[],[f56,f57])).

fof(f1267,plain,
    ( spl6_122
    | ~ spl6_112 ),
    inference(avatar_split_clause,[],[f1251,f1223,f1265])).

fof(f1251,plain,
    ( m1_subset_1(sK5(k1_relat_1(sK2)),sK0)
    | ~ spl6_112 ),
    inference(resolution,[],[f1224,f76])).

fof(f1260,plain,
    ( spl6_66
    | spl6_120
    | spl6_110
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f474,f243,f105,f84,f1220,f1253,f514])).

fof(f1220,plain,
    ( spl6_110
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f474,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k1_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0)
        | ~ r1_partfun1(sK2,X1) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(forward_demodulation,[],[f473,f244])).

fof(f473,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0)
        | ~ r1_partfun1(sK2,X1)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK2)) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f472,f106])).

fof(f472,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0)
        | ~ r1_partfun1(sK2,X1)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_0
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f467,f85])).

fof(f467,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0)
        | ~ r1_partfun1(sK2,X1)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_36 ),
    inference(superposition,[],[f228,f244])).

fof(f1255,plain,
    ( spl6_120
    | spl6_110
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36
    | spl6_67 ),
    inference(avatar_split_clause,[],[f1121,f511,f243,f105,f84,f1220,f1253])).

fof(f1121,plain,
    ( ! [X8,X7] :
        ( v1_xboole_0(k1_relat_1(sK2))
        | ~ m1_subset_1(X7,k1_relat_1(sK2))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_funct_1(sK2,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK2,X8) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_67 ),
    inference(forward_demodulation,[],[f1120,f244])).

fof(f1120,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK2))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_funct_1(sK2,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK2,X8)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK2)) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f1119,f106])).

fof(f1119,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK2))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_funct_1(sK2,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK2,X8)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_0
    | ~ spl6_36
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f1118,f85])).

fof(f1118,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK2))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(sK2)
        | k1_funct_1(sK2,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK2,X8)
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_36
    | ~ spl6_67 ),
    inference(subsumption_resolution,[],[f1117,f512])).

fof(f1245,plain,
    ( spl6_66
    | spl6_118
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f643,f250,f112,f91,f1243,f514])).

fof(f643,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK1,X0) = k1_funct_1(X1,X0)
        | ~ r1_partfun1(sK1,X1) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f642,f92])).

fof(f642,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK1)
        | k1_funct_1(sK1,X0) = k1_funct_1(X1,X0)
        | ~ r1_partfun1(sK1,X1) )
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f611,f113])).

fof(f611,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK1)
        | k1_funct_1(sK1,X0) = k1_funct_1(X1,X0)
        | ~ r1_partfun1(sK1,X1) )
    | ~ spl6_38 ),
    inference(superposition,[],[f56,f251])).

fof(f1237,plain,
    ( spl6_66
    | spl6_116
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38
    | spl6_43 ),
    inference(avatar_split_clause,[],[f635,f260,f250,f112,f91,f1235,f514])).

fof(f635,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_relat_1(sK1))
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,sK0,sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK1,X7) = k1_funct_1(X8,X7)
        | ~ r1_partfun1(sK1,X8) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f634,f261])).

fof(f1229,plain,
    ( spl6_66
    | spl6_114
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f270,f243,f105,f84,f1227,f514])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0)
        | ~ r1_partfun1(sK2,X1) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f269,f85])).

fof(f269,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0)
        | ~ r1_partfun1(sK2,X1) )
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f266,f106])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0)
        | ~ r1_partfun1(sK2,X1) )
    | ~ spl6_36 ),
    inference(superposition,[],[f56,f244])).

fof(f1225,plain,
    ( spl6_110
    | spl6_112
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f721,f286,f1223,f1220])).

fof(f721,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK0)
        | v1_xboole_0(k1_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_relat_1(sK2)) )
    | ~ spl6_44 ),
    inference(resolution,[],[f355,f68])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | m1_subset_1(X0,sK0) )
    | ~ spl6_44 ),
    inference(resolution,[],[f287,f66])).

fof(f1215,plain,
    ( spl6_66
    | spl6_86
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f985,f243,f105,f84,f835,f514])).

fof(f985,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k1_relat_1(sK2),sK4(sK0,sK0,sK2,X5))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,sK0,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X5) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f984,f106])).

fof(f984,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k1_relat_1(sK2),sK4(sK0,sK0,sK2,X5))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,sK0,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X5)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_0
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f929,f85])).

fof(f929,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k1_relat_1(sK2),sK4(sK0,sK0,sK2,X5))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,sK0,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X5)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_36 ),
    inference(superposition,[],[f208,f244])).

fof(f1214,plain,
    ( spl6_66
    | spl6_92
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f983,f243,f105,f84,f974,f514])).

fof(f983,plain,
    ( ! [X6] :
        ( m1_subset_1(sK4(sK0,sK0,sK2,X6),k1_relat_1(sK2))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,sK0,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X6) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f982,f106])).

fof(f982,plain,
    ( ! [X6] :
        ( m1_subset_1(sK4(sK0,sK0,sK2,X6),k1_relat_1(sK2))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,sK0,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X6)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_0
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f930,f85])).

fof(f930,plain,
    ( ! [X6] :
        ( m1_subset_1(sK4(sK0,sK0,sK2,X6),k1_relat_1(sK2))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,sK0,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X6)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_36 ),
    inference(superposition,[],[f209,f244])).

fof(f1213,plain,
    ( spl6_66
    | spl6_82
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f844,f243,f105,f84,f731,f514])).

fof(f844,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK2,X2),k1_relat_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X2) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f843,f85])).

fof(f843,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK2,X2),k1_relat_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X2) )
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f795,f106])).

fof(f795,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK2,X2),k1_relat_1(sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X2) )
    | ~ spl6_36 ),
    inference(superposition,[],[f57,f244])).

fof(f1204,plain,
    ( spl6_66
    | spl6_108
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f641,f250,f112,f91,f1202,f514])).

fof(f1202,plain,
    ( spl6_108
  <=> ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK1,X2),k1_relat_1(sK1))
        | r1_partfun1(sK1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f641,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK1,X2),k1_relat_1(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK1,X2) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f640,f92])).

fof(f640,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK1,X2),k1_relat_1(sK1))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK1)
        | r1_partfun1(sK1,X2) )
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f612,f113])).

fof(f612,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK1,X2),k1_relat_1(sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK1)
        | r1_partfun1(sK1,X2) )
    | ~ spl6_38 ),
    inference(superposition,[],[f57,f251])).

fof(f1197,plain,
    ( spl6_66
    | spl6_106
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f639,f250,f112,f91,f1195,f514])).

fof(f1195,plain,
    ( spl6_106
  <=> ! [X5] :
        ( ~ r2_hidden(k1_relat_1(sK1),sK4(sK0,sK0,sK1,X5))
        | r1_partfun1(sK1,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_2(X5,sK0,sK0)
        | ~ v1_funct_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).

fof(f639,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k1_relat_1(sK1),sK4(sK0,sK0,sK1,X5))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,sK0,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK1,X5) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f638,f113])).

fof(f638,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k1_relat_1(sK1),sK4(sK0,sK0,sK1,X5))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,sK0,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK1,X5)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f616,f92])).

fof(f616,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k1_relat_1(sK1),sK4(sK0,sK0,sK1,X5))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,sK0,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK1)
        | r1_partfun1(sK1,X5)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_38 ),
    inference(superposition,[],[f208,f251])).

fof(f1192,plain,
    ( spl6_66
    | spl6_104
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f637,f250,f112,f91,f1190,f514])).

fof(f637,plain,
    ( ! [X6] :
        ( m1_subset_1(sK4(sK0,sK0,sK1,X6),k1_relat_1(sK1))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,sK0,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK1,X6) )
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f636,f113])).

fof(f636,plain,
    ( ! [X6] :
        ( m1_subset_1(sK4(sK0,sK0,sK1,X6),k1_relat_1(sK1))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,sK0,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK1,X6)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f617,f92])).

fof(f617,plain,
    ( ! [X6] :
        ( m1_subset_1(sK4(sK0,sK0,sK1,X6),k1_relat_1(sK1))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,sK0,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK1)
        | r1_partfun1(sK1,X6)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_38 ),
    inference(superposition,[],[f209,f251])).

fof(f1183,plain,
    ( spl6_102
    | ~ spl6_8
    | ~ spl6_38
    | spl6_43 ),
    inference(avatar_split_clause,[],[f971,f260,f250,f112,f1181])).

fof(f971,plain,
    ( m1_subset_1(sK5(k1_relat_1(sK1)),sK0)
    | ~ spl6_8
    | ~ spl6_38
    | ~ spl6_43 ),
    inference(resolution,[],[f521,f76])).

fof(f1176,plain,
    ( spl6_66
    | spl6_78
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f981,f105,f98,f84,f629,f514])).

fof(f981,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f980,f99])).

fof(f980,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f897,f85])).

fof(f897,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f106,f210])).

fof(f1166,plain,
    ( spl6_100
    | ~ spl6_84
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f1154,f948,f771,f1164])).

fof(f948,plain,
    ( spl6_90
  <=> k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f1154,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_84
    | ~ spl6_90 ),
    inference(subsumption_resolution,[],[f1137,f772])).

fof(f1137,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_90 ),
    inference(superposition,[],[f71,f949])).

fof(f949,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_relat_1(sK2)
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f948])).

fof(f1064,plain,
    ( ~ spl6_88
    | spl6_99 ),
    inference(avatar_contradiction_clause,[],[f1063])).

fof(f1063,plain,
    ( $false
    | ~ spl6_88
    | ~ spl6_99 ),
    inference(subsumption_resolution,[],[f1056,f1036])).

fof(f1036,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_relat_1(sK1)
    | ~ spl6_88 ),
    inference(resolution,[],[f878,f72])).

fof(f1056,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_relat_1(sK1)
    | ~ spl6_99 ),
    inference(avatar_component_clause,[],[f1055])).

fof(f1055,plain,
    ( spl6_99
  <=> k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) != k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f1060,plain,
    ( spl6_98
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f651,f514,f250,f1058])).

fof(f651,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) = k1_relat_1(sK1)
    | ~ spl6_38
    | ~ spl6_66 ),
    inference(backward_demodulation,[],[f515,f251])).

fof(f1053,plain,
    ( ~ spl6_97
    | ~ spl6_66
    | spl6_69 ),
    inference(avatar_split_clause,[],[f667,f523,f514,f1051])).

fof(f1051,plain,
    ( spl6_97
  <=> ~ m1_subset_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f523,plain,
    ( spl6_69
  <=> ~ m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f667,plain,
    ( ~ m1_subset_1(sK3,k1_xboole_0)
    | ~ spl6_66
    | ~ spl6_69 ),
    inference(backward_demodulation,[],[f515,f524])).

fof(f524,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | ~ spl6_69 ),
    inference(avatar_component_clause,[],[f523])).

fof(f1046,plain,
    ( ~ spl6_95
    | spl6_31
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f649,f514,f222,f1044])).

fof(f1044,plain,
    ( spl6_95
  <=> ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f649,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl6_31
    | ~ spl6_66 ),
    inference(backward_demodulation,[],[f515,f223])).

fof(f976,plain,
    ( spl6_66
    | spl6_92
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f452,f243,f105,f84,f974,f514])).

fof(f452,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,sK0,sK2,X0),k1_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X0) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f451,f106])).

fof(f451,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,sK0,sK2,X0),k1_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_0
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f448,f85])).

fof(f448,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,sK0,sK2,X0),k1_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_36 ),
    inference(superposition,[],[f209,f244])).

fof(f965,plain,
    ( spl6_66
    | spl6_78
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f842,f105,f98,f84,f629,f514])).

fof(f842,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f841,f99])).

fof(f841,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f781,f85])).

fof(f781,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f106,f210])).

fof(f950,plain,
    ( spl6_90
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f916,f771,f948])).

fof(f916,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) = k1_relat_1(sK2)
    | ~ spl6_84 ),
    inference(resolution,[],[f772,f72])).

fof(f879,plain,
    ( spl6_88
    | ~ spl6_8
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f646,f514,f112,f877])).

fof(f646,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_8
    | ~ spl6_66 ),
    inference(backward_demodulation,[],[f515,f113])).

fof(f837,plain,
    ( spl6_66
    | spl6_86
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f444,f243,f105,f84,f835,f514])).

fof(f444,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_relat_1(sK2),sK4(sK0,sK0,sK2,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X0) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f443,f106])).

fof(f443,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_relat_1(sK2),sK4(sK0,sK0,sK2,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_0
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f440,f85])).

fof(f440,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_relat_1(sK2),sK4(sK0,sK0,sK2,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl6_36 ),
    inference(superposition,[],[f208,f244])).

fof(f827,plain,
    ( spl6_66
    | spl6_78
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f738,f105,f98,f84,f629,f514])).

fof(f738,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f737,f99])).

fof(f737,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f683,f85])).

fof(f683,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X2)
        | r1_partfun1(X2,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X2)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f106,f210])).

fof(f773,plain,
    ( spl6_84
    | ~ spl6_6
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f645,f514,f105,f771])).

fof(f645,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_6
    | ~ spl6_66 ),
    inference(backward_demodulation,[],[f515,f106])).

fof(f733,plain,
    ( spl6_66
    | spl6_82
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f272,f243,f105,f84,f731,f514])).

fof(f272,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK2,X2),k1_relat_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | r1_partfun1(sK2,X2) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f271,f85])).

fof(f271,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK2,X2),k1_relat_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X2) )
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f267,f106])).

fof(f267,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK0,sK0,sK2,X2),k1_relat_1(sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(sK2)
        | r1_partfun1(sK2,X2) )
    | ~ spl6_36 ),
    inference(superposition,[],[f57,f244])).

fof(f681,plain,
    ( spl6_80
    | ~ spl6_4
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f644,f514,f98,f679])).

fof(f644,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_66 ),
    inference(backward_demodulation,[],[f515,f99])).

fof(f631,plain,
    ( spl6_66
    | spl6_78
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f430,f105,f98,f84,f629,f514])).

fof(f430,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X0)
        | r1_partfun1(X0,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X0)) )
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f429,f99])).

fof(f429,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X0)
        | r1_partfun1(X0,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X0)) )
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f425,f85])).

fof(f425,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k1_xboole_0 = sK0
        | ~ v1_funct_1(X0)
        | r1_partfun1(X0,sK2)
        | ~ v1_xboole_0(k1_relset_1(sK0,sK0,X0)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f210,f106])).

fof(f624,plain,
    ( spl6_42
    | spl6_46
    | ~ spl6_18
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f532,f250,f143,f290,f263])).

fof(f532,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
        | v1_xboole_0(k1_relat_1(sK1))
        | ~ m1_subset_1(X0,k1_relat_1(sK1)) )
    | ~ spl6_18
    | ~ spl6_38 ),
    inference(resolution,[],[f313,f68])).

fof(f603,plain,
    ( spl6_76
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f575,f263,f601])).

fof(f575,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_42 ),
    inference(backward_demodulation,[],[f571,f264])).

fof(f568,plain,
    ( spl6_74
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f409,f290,f566])).

fof(f566,plain,
    ( spl6_74
  <=> k1_funct_1(sK1,sK5(k1_relat_1(sK1))) = k1_funct_1(sK2,sK5(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f409,plain,
    ( k1_funct_1(sK1,sK5(k1_relat_1(sK1))) = k1_funct_1(sK2,sK5(k1_relat_1(sK1)))
    | ~ spl6_46 ),
    inference(resolution,[],[f291,f76])).

fof(f557,plain,
    ( ~ spl6_2
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f556])).

fof(f556,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f552,f92])).

fof(f552,plain,
    ( ~ v1_funct_1(sK1)
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(resolution,[],[f169,f182])).

fof(f169,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_22
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f555,plain,
    ( ~ spl6_0
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f551,f85])).

fof(f551,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(resolution,[],[f169,f165])).

fof(f550,plain,
    ( ~ spl6_2
    | ~ spl6_24
    | ~ spl6_26
    | spl6_71 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_24
    | ~ spl6_26
    | ~ spl6_71 ),
    inference(subsumption_resolution,[],[f548,f92])).

fof(f548,plain,
    ( ~ v1_funct_1(sK1)
    | ~ spl6_24
    | ~ spl6_26
    | ~ spl6_71 ),
    inference(subsumption_resolution,[],[f547,f182])).

fof(f547,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl6_24
    | ~ spl6_71 ),
    inference(resolution,[],[f536,f172])).

fof(f172,plain,
    ( ! [X0] :
        ( r1_partfun1(X0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_24
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_partfun1(X0,X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f536,plain,
    ( ~ r1_partfun1(sK1,sK1)
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl6_71
  <=> ~ r1_partfun1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f546,plain,
    ( spl6_70
    | spl6_66
    | ~ spl6_73
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f389,f112,f91,f544,f514,f538])).

fof(f538,plain,
    ( spl6_70
  <=> r1_partfun1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f389,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | r1_partfun1(sK1,sK1)
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f384,f92])).

fof(f384,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | k1_xboole_0 = sK0
    | r1_partfun1(sK1,sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f234,f113])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | k1_xboole_0 = X2
      | r1_partfun1(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X0)
      | r1_partfun1(X0,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f528,plain,
    ( spl6_68
    | ~ spl6_8
    | ~ spl6_28
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f520,f250,f195,f112,f526])).

fof(f520,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl6_8
    | ~ spl6_28
    | ~ spl6_38 ),
    inference(resolution,[],[f364,f196])).

fof(f516,plain,
    ( spl6_64
    | spl6_66
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f388,f105,f98,f84,f514,f508])).

fof(f508,plain,
    ( spl6_64
  <=> r1_partfun1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f388,plain,
    ( k1_xboole_0 = sK0
    | r1_partfun1(sK2,sK2)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f387,f99])).

fof(f387,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | k1_xboole_0 = sK0
    | r1_partfun1(sK2,sK2)
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f383,f85])).

fof(f383,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | k1_xboole_0 = sK0
    | r1_partfun1(sK2,sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f234,f106])).

fof(f503,plain,
    ( ~ spl6_59
    | spl6_62
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f351,f250,f112,f501,f487])).

fof(f351,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ v1_xboole_0(sK0) )
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f347,f113])).

fof(f347,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_xboole_0(sK0) )
    | ~ spl6_38 ),
    inference(superposition,[],[f176,f251])).

fof(f492,plain,
    ( ~ spl6_59
    | spl6_60
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f350,f243,f105,f490,f487])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_xboole_0(sK0) )
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f346,f106])).

fof(f346,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_xboole_0(sK0) )
    | ~ spl6_36 ),
    inference(superposition,[],[f176,f244])).

fof(f437,plain,
    ( spl6_10
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f415,f308,f181,f164,f91,f84,f116])).

fof(f419,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_11
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_48 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_48 ),
    inference(subsumption_resolution,[],[f120,f415])).

fof(f411,plain,
    ( spl6_15
    | ~ spl6_40
    | ~ spl6_46 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl6_15
    | ~ spl6_40
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f408,f133])).

fof(f408,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl6_40
    | ~ spl6_46 ),
    inference(resolution,[],[f291,f255])).

fof(f407,plain,
    ( ~ spl6_55
    | spl6_56
    | spl6_51 ),
    inference(avatar_split_clause,[],[f329,f325,f405,f399])).

fof(f405,plain,
    ( spl6_56
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f329,plain,
    ( v1_xboole_0(sK3)
    | ~ m1_subset_1(k1_relat_1(sK1),sK3)
    | ~ spl6_51 ),
    inference(resolution,[],[f326,f68])).

fof(f341,plain,
    ( spl6_52
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f281,f250,f112,f339])).

fof(f281,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl6_8
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f276,f113])).

fof(f276,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_38 ),
    inference(superposition,[],[f71,f251])).

fof(f328,plain,
    ( spl6_40
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f300,f195,f254])).

fof(f300,plain,
    ( m1_subset_1(sK3,k1_relat_1(sK1))
    | ~ spl6_28 ),
    inference(resolution,[],[f196,f69])).

fof(f327,plain,
    ( ~ spl6_51
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f299,f195,f325])).

fof(f299,plain,
    ( ~ r2_hidden(k1_relat_1(sK1),sK3)
    | ~ spl6_28 ),
    inference(resolution,[],[f196,f70])).

fof(f318,plain,
    ( ~ spl6_8
    | spl6_15
    | ~ spl6_18
    | ~ spl6_28 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f316,f133])).

fof(f316,plain,
    ( k1_funct_1(sK1,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_28 ),
    inference(resolution,[],[f190,f196])).

fof(f190,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK1))
        | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3) )
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f185,f144])).

fof(f185,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f72,f113])).

fof(f314,plain,
    ( ~ spl6_43
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f301,f195,f260])).

fof(f301,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl6_28 ),
    inference(resolution,[],[f196,f67])).

fof(f312,plain,
    ( ~ spl6_28
    | ~ spl6_42 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | ~ spl6_28
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f264,f301])).

fof(f310,plain,
    ( spl6_48
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f298,f181,f164,f116,f91,f84,f308])).

fof(f298,plain,
    ( r1_partfun1(sK2,sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f297,f182])).

fof(f297,plain,
    ( ~ v1_relat_1(sK1)
    | r1_partfun1(sK2,sK1)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f296,f85])).

fof(f296,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | r1_partfun1(sK2,sK1)
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f295,f165])).

fof(f295,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | r1_partfun1(sK2,sK1)
    | ~ spl6_2
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f294,f92])).

fof(f294,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | r1_partfun1(sK2,sK1)
    | ~ spl6_10 ),
    inference(resolution,[],[f117,f73])).

fof(f303,plain,
    ( ~ spl6_28
    | spl6_41 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl6_28
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f300,f258])).

fof(f258,plain,
    ( ~ m1_subset_1(sK3,k1_relat_1(sK1))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl6_41
  <=> ~ m1_subset_1(sK3,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f292,plain,
    ( spl6_46
    | spl6_42
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f192,f143,f112,f263,f290])).

fof(f192,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_relat_1(sK1))
        | ~ m1_subset_1(X0,k1_relat_1(sK1))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) )
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f188,f185])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_relat_1(sK1))
        | v1_xboole_0(k1_relset_1(sK0,sK0,sK1))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) )
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f185,f147])).

fof(f147,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_relset_1(sK0,sK0,sK1))
        | ~ m1_subset_1(X0,k1_relset_1(sK0,sK0,sK1))
        | k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0) )
    | ~ spl6_18 ),
    inference(resolution,[],[f68,f144])).

fof(f288,plain,
    ( spl6_44
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f273,f243,f105,f286])).

fof(f273,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f268,f106])).

fof(f268,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_36 ),
    inference(superposition,[],[f71,f244])).

fof(f265,plain,
    ( ~ spl6_41
    | spl6_42
    | ~ spl6_8
    | spl6_13 ),
    inference(avatar_split_clause,[],[f193,f122,f112,f263,f257])).

fof(f122,plain,
    ( spl6_13
  <=> ~ r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f193,plain,
    ( v1_xboole_0(k1_relat_1(sK1))
    | ~ m1_subset_1(sK3,k1_relat_1(sK1))
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f189,f185])).

fof(f189,plain,
    ( ~ m1_subset_1(sK3,k1_relat_1(sK1))
    | v1_xboole_0(k1_relset_1(sK0,sK0,sK1))
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f185,f146])).

fof(f146,plain,
    ( v1_xboole_0(k1_relset_1(sK0,sK0,sK1))
    | ~ m1_subset_1(sK3,k1_relset_1(sK0,sK0,sK1))
    | ~ spl6_13 ),
    inference(resolution,[],[f68,f123])).

fof(f123,plain,
    ( ~ r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f252,plain,
    ( spl6_38
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f185,f112,f250])).

fof(f245,plain,
    ( spl6_36
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f184,f105,f243])).

fof(f184,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f72,f106])).

fof(f238,plain,
    ( ~ spl6_31
    | spl6_34
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f155,f112,f236,f222])).

fof(f236,plain,
    ( spl6_34
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f155,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0)) )
    | ~ spl6_8 ),
    inference(resolution,[],[f65,f113])).

fof(f227,plain,
    ( ~ spl6_31
    | spl6_32
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f154,f105,f225,f222])).

fof(f225,plain,
    ( spl6_32
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK0)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f65,f106])).

fof(f200,plain,
    ( ~ spl6_29
    | ~ spl6_8
    | spl6_13 ),
    inference(avatar_split_clause,[],[f191,f122,f112,f198])).

fof(f191,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f185,f123])).

fof(f183,plain,
    ( spl6_26
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f152,f112,f181])).

fof(f152,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f75,f113])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',cc1_relset_1)).

fof(f173,plain,
    ( spl6_22
    | spl6_24 ),
    inference(avatar_split_clause,[],[f74,f171,f168])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r1_partfun1(X0,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => r1_partfun1(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',reflexivity_r1_partfun1)).

fof(f166,plain,
    ( spl6_20
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f151,f105,f164])).

fof(f151,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f75,f106])).

fof(f145,plain,
    ( spl6_10
    | spl6_18 ),
    inference(avatar_split_clause,[],[f50,f143,f116])).

fof(f50,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK0,sK0,sK1))
      | k1_funct_1(sK1,X3) = k1_funct_1(sK2,X3)
      | r1_partfun1(sK1,sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_partfun1(X1,X2)
          <~> ! [X3] :
                ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                | ~ r2_hidden(X3,k1_relset_1(X0,X0,X1)) ) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
            <=> ! [X3] :
                  ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relset_1(X0,X0,X1))
               => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',t146_funct_2)).

fof(f141,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f64,f139])).

fof(f139,plain,
    ( spl6_16
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f64,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t146_funct_2.p',d2_xboole_0)).

fof(f134,plain,
    ( ~ spl6_11
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f49,f132,f119])).

fof(f49,plain,
    ( k1_funct_1(sK1,sK3) != k1_funct_1(sK2,sK3)
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f127,plain,
    ( ~ spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f48,f125,f119])).

fof(f125,plain,
    ( spl6_12
  <=> r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f48,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK0,sK1))
    | ~ r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f114,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f107,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f53,f105])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f52,f98])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f54,f91])).

fof(f54,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f51,f84])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
