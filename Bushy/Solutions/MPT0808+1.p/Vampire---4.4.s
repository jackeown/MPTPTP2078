%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t61_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:15 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  608 (2093 expanded)
%              Number of leaves         :  154 ( 888 expanded)
%              Depth                    :   15
%              Number of atoms          : 1925 (6070 expanded)
%              Number of equality atoms :   89 ( 378 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2369,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f122,f129,f136,f143,f150,f157,f164,f171,f181,f217,f226,f238,f245,f252,f259,f269,f282,f295,f303,f322,f333,f345,f352,f414,f430,f446,f461,f469,f481,f491,f498,f540,f549,f556,f571,f587,f603,f612,f619,f629,f645,f661,f670,f677,f687,f703,f719,f728,f735,f753,f798,f818,f834,f842,f852,f855,f874,f907,f932,f956,f965,f972,f1006,f1054,f1118,f1126,f1134,f1141,f1159,f1195,f1240,f1251,f1257,f1271,f1281,f1291,f1299,f1315,f1331,f1340,f1347,f1374,f1378,f1382,f1395,f1396,f1473,f1498,f1508,f1523,f1538,f1554,f1571,f1586,f1603,f1640,f1643,f1651,f1672,f1697,f1712,f1727,f1766,f1778,f1781,f1972,f1980,f1983,f1995,f2037,f2086,f2109,f2127,f2137,f2150,f2252,f2307,f2320,f2333,f2344,f2353,f2366,f2368])).

fof(f2368,plain,
    ( ~ spl6_0
    | ~ spl6_80
    | spl6_247 ),
    inference(avatar_contradiction_clause,[],[f2367])).

fof(f2367,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_80
    | ~ spl6_247 ),
    inference(subsumption_resolution,[],[f2365,f2292])).

fof(f2292,plain,
    ( ! [X0] : r1_tarski(k1_wellord1(sK0,X0),k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_80 ),
    inference(resolution,[],[f2285,f2159])).

fof(f2159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | r1_tarski(X0,k3_relat_1(sK0)) )
    | ~ spl6_80 ),
    inference(superposition,[],[f102,f586])).

fof(f586,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k3_relat_1(sK0))
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f585])).

fof(f585,plain,
    ( spl6_80
  <=> k1_xboole_0 = k1_zfmisc_1(k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t3_subset)).

fof(f2285,plain,
    ( ! [X0] : m1_subset_1(k1_wellord1(sK0,X0),k1_xboole_0)
    | ~ spl6_0
    | ~ spl6_80 ),
    inference(subsumption_resolution,[],[f2280,f114])).

fof(f114,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f2280,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_wellord1(sK0,X0),k1_xboole_0)
        | ~ v1_relat_1(sK0) )
    | ~ spl6_80 ),
    inference(resolution,[],[f2160,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t13_wellord1)).

fof(f2160,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k3_relat_1(sK0))
        | m1_subset_1(X1,k1_xboole_0) )
    | ~ spl6_80 ),
    inference(superposition,[],[f103,f586])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f2365,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ spl6_247 ),
    inference(avatar_component_clause,[],[f2364])).

fof(f2364,plain,
    ( spl6_247
  <=> ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_247])])).

fof(f2366,plain,
    ( ~ spl6_247
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | spl6_197 ),
    inference(avatar_split_clause,[],[f2155,f1638,f162,f141,f134,f127,f120,f113,f2364])).

fof(f120,plain,
    ( spl6_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f127,plain,
    ( spl6_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f134,plain,
    ( spl6_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f141,plain,
    ( spl6_8
  <=> v2_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f162,plain,
    ( spl6_14
  <=> r3_wellord1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f1638,plain,
    ( spl6_197
  <=> ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_197])])).

fof(f2155,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2154,f114])).

fof(f2154,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2153,f121])).

fof(f121,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f2153,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2152,f128])).

fof(f128,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f2152,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2151,f135])).

fof(f135,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f2151,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2143,f142])).

fof(f142,plain,
    ( v2_wellord1(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f141])).

fof(f2143,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_14
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2142,f163])).

fof(f163,plain,
    ( r3_wellord1(sK0,sK1,sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f162])).

fof(f2142,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_197 ),
    inference(resolution,[],[f1639,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
      | ~ r3_wellord1(X1,X2,X3)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) )
              | ~ r3_wellord1(X1,X2,X3)
              | ~ r1_tarski(X0,k3_relat_1(X1))
              | ~ v2_wellord1(X1)
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) )
              | ~ r3_wellord1(X1,X2,X3)
              | ~ r1_tarski(X0,k3_relat_1(X1))
              | ~ v2_wellord1(X1)
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( r3_wellord1(X1,X2,X3)
                  & r1_tarski(X0,k3_relat_1(X1))
                  & v2_wellord1(X1) )
               => ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                  & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t59_wellord1)).

fof(f1639,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ spl6_197 ),
    inference(avatar_component_clause,[],[f1638])).

fof(f2353,plain,
    ( spl6_238
    | ~ spl6_245
    | ~ spl6_80
    | ~ spl6_190 ),
    inference(avatar_split_clause,[],[f2194,f1584,f585,f2351,f2325])).

fof(f2325,plain,
    ( spl6_238
  <=> m1_subset_1(k1_xboole_0,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_238])])).

fof(f2351,plain,
    ( spl6_245
  <=> ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_245])])).

fof(f1584,plain,
    ( spl6_190
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_190])])).

fof(f2194,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK1)),k1_xboole_0)
    | m1_subset_1(k1_xboole_0,k3_relat_1(sK0))
    | ~ spl6_80
    | ~ spl6_190 ),
    inference(superposition,[],[f1591,f586])).

fof(f1591,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK1)),k1_zfmisc_1(X0))
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl6_190 ),
    inference(resolution,[],[f1585,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t4_subset)).

fof(f1585,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k3_relat_1(sK1)))
    | ~ spl6_190 ),
    inference(avatar_component_clause,[],[f1584])).

fof(f2344,plain,
    ( spl6_238
    | ~ spl6_243
    | ~ spl6_80
    | ~ spl6_162 ),
    inference(avatar_split_clause,[],[f2182,f1313,f585,f2342,f2325])).

fof(f2342,plain,
    ( spl6_243
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_243])])).

fof(f1313,plain,
    ( spl6_162
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_162])])).

fof(f2182,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | m1_subset_1(k1_xboole_0,k3_relat_1(sK0))
    | ~ spl6_80
    | ~ spl6_162 ),
    inference(superposition,[],[f1321,f586])).

fof(f1321,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0))
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl6_162 ),
    inference(resolution,[],[f1314,f106])).

fof(f1314,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_162 ),
    inference(avatar_component_clause,[],[f1313])).

fof(f2333,plain,
    ( spl6_238
    | ~ spl6_241
    | ~ spl6_42
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f2180,f585,f320,f2331,f2325])).

fof(f2331,plain,
    ( spl6_241
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_241])])).

fof(f320,plain,
    ( spl6_42
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f2180,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | m1_subset_1(k1_xboole_0,k3_relat_1(sK0))
    | ~ spl6_42
    | ~ spl6_80 ),
    inference(superposition,[],[f1146,f586])).

fof(f1146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0))
        | m1_subset_1(k1_xboole_0,X0) )
    | ~ spl6_42 ),
    inference(resolution,[],[f321,f106])).

fof(f321,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f320])).

fof(f2320,plain,
    ( ~ spl6_237
    | ~ spl6_80
    | spl6_115
    | spl6_151 ),
    inference(avatar_split_clause,[],[f2230,f1129,f748,f585,f2318])).

fof(f2318,plain,
    ( spl6_237
  <=> ~ r2_hidden(k3_relat_1(sK0),sK5(sK5(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_237])])).

fof(f748,plain,
    ( spl6_115
  <=> ~ v1_xboole_0(k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).

fof(f1129,plain,
    ( spl6_151
  <=> ~ v1_xboole_0(sK5(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_151])])).

fof(f2230,plain,
    ( ~ r2_hidden(k3_relat_1(sK0),sK5(sK5(k1_xboole_0)))
    | ~ spl6_80
    | ~ spl6_115
    | ~ spl6_151 ),
    inference(subsumption_resolution,[],[f2229,f1130])).

fof(f1130,plain,
    ( ~ v1_xboole_0(sK5(k1_xboole_0))
    | ~ spl6_151 ),
    inference(avatar_component_clause,[],[f1129])).

fof(f2229,plain,
    ( v1_xboole_0(sK5(k1_xboole_0))
    | ~ r2_hidden(k3_relat_1(sK0),sK5(sK5(k1_xboole_0)))
    | ~ spl6_80
    | ~ spl6_115 ),
    inference(forward_demodulation,[],[f2228,f586])).

fof(f2228,plain,
    ( ~ r2_hidden(k3_relat_1(sK0),sK5(sK5(k1_xboole_0)))
    | v1_xboole_0(sK5(k1_zfmisc_1(k3_relat_1(sK0))))
    | ~ spl6_80
    | ~ spl6_115 ),
    inference(subsumption_resolution,[],[f2176,f749])).

fof(f749,plain,
    ( ~ v1_xboole_0(k3_relat_1(sK0))
    | ~ spl6_115 ),
    inference(avatar_component_clause,[],[f748])).

fof(f2176,plain,
    ( ~ r2_hidden(k3_relat_1(sK0),sK5(sK5(k1_xboole_0)))
    | v1_xboole_0(sK5(k1_zfmisc_1(k3_relat_1(sK0))))
    | v1_xboole_0(k3_relat_1(sK0))
    | ~ spl6_80 ),
    inference(superposition,[],[f502,f586])).

fof(f502,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK5(sK5(k1_zfmisc_1(X4))))
      | v1_xboole_0(sK5(k1_zfmisc_1(X4)))
      | v1_xboole_0(X4) ) ),
    inference(resolution,[],[f387,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',antisymmetry_r2_hidden)).

fof(f387,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK5(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK5(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f362,f89])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',existence_m1_subset_1)).

fof(f362,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | v1_xboole_0(X3)
      | v1_xboole_0(X4)
      | r2_hidden(sK5(X3),X4) ) ),
    inference(resolution,[],[f335,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t2_subset)).

fof(f335,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK5(X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f106,f202])).

fof(f202,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f99,f89])).

fof(f2307,plain,
    ( spl6_234
    | ~ spl6_80
    | spl6_115
    | spl6_151 ),
    inference(avatar_split_clause,[],[f2225,f1129,f748,f585,f2305])).

fof(f2305,plain,
    ( spl6_234
  <=> r2_hidden(sK5(sK5(k1_xboole_0)),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_234])])).

fof(f2225,plain,
    ( r2_hidden(sK5(sK5(k1_xboole_0)),k3_relat_1(sK0))
    | ~ spl6_80
    | ~ spl6_115
    | ~ spl6_151 ),
    inference(subsumption_resolution,[],[f2224,f1130])).

fof(f2224,plain,
    ( v1_xboole_0(sK5(k1_xboole_0))
    | r2_hidden(sK5(sK5(k1_xboole_0)),k3_relat_1(sK0))
    | ~ spl6_80
    | ~ spl6_115 ),
    inference(forward_demodulation,[],[f2223,f586])).

fof(f2223,plain,
    ( r2_hidden(sK5(sK5(k1_xboole_0)),k3_relat_1(sK0))
    | v1_xboole_0(sK5(k1_zfmisc_1(k3_relat_1(sK0))))
    | ~ spl6_80
    | ~ spl6_115 ),
    inference(subsumption_resolution,[],[f2171,f749])).

fof(f2171,plain,
    ( r2_hidden(sK5(sK5(k1_xboole_0)),k3_relat_1(sK0))
    | v1_xboole_0(k3_relat_1(sK0))
    | v1_xboole_0(sK5(k1_zfmisc_1(k3_relat_1(sK0))))
    | ~ spl6_80 ),
    inference(superposition,[],[f387,f586])).

fof(f2252,plain,
    ( ~ spl6_233
    | ~ spl6_80
    | spl6_121 ),
    inference(avatar_split_clause,[],[f2158,f832,f585,f2250])).

fof(f2250,plain,
    ( spl6_233
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_233])])).

fof(f832,plain,
    ( spl6_121
  <=> ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f2158,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_80
    | ~ spl6_121 ),
    inference(superposition,[],[f833,f586])).

fof(f833,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK0)),k1_xboole_0)
    | ~ spl6_121 ),
    inference(avatar_component_clause,[],[f832])).

fof(f2150,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_76
    | spl6_197 ),
    inference(avatar_contradiction_clause,[],[f2149])).

fof(f2149,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_76
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2148,f114])).

fof(f2148,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_76
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2147,f121])).

fof(f2147,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_76
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2146,f128])).

fof(f2146,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_76
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2145,f135])).

fof(f2145,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_76
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2144,f142])).

fof(f2144,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_14
    | ~ spl6_76
    | ~ spl6_197 ),
    inference(subsumption_resolution,[],[f2143,f589])).

fof(f589,plain,
    ( ! [X1] : r1_tarski(k1_wellord1(sK0,X1),k3_relat_1(sK0))
    | ~ spl6_76 ),
    inference(resolution,[],[f564,f199])).

fof(f199,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X2))
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f102,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t1_subset)).

fof(f564,plain,
    ( ! [X6] : r2_hidden(k1_wellord1(sK0,X6),k1_zfmisc_1(k3_relat_1(sK0)))
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f563])).

fof(f563,plain,
    ( spl6_76
  <=> ! [X6] : r2_hidden(k1_wellord1(sK0,X6),k1_zfmisc_1(k3_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f2137,plain,
    ( spl6_230
    | ~ spl6_226 ),
    inference(avatar_split_clause,[],[f2120,f2107,f2135])).

fof(f2135,plain,
    ( spl6_230
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_230])])).

fof(f2107,plain,
    ( spl6_226
  <=> k1_xboole_0 = sK5(k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_226])])).

fof(f2120,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ spl6_226 ),
    inference(superposition,[],[f89,f2108])).

fof(f2108,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ spl6_226 ),
    inference(avatar_component_clause,[],[f2107])).

fof(f2127,plain,
    ( spl6_228
    | ~ spl6_226 ),
    inference(avatar_split_clause,[],[f2116,f2107,f2125])).

fof(f2125,plain,
    ( spl6_228
  <=> r1_tarski(k1_xboole_0,k9_relat_1(sK2,k1_wellord1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_228])])).

fof(f2116,plain,
    ( r1_tarski(k1_xboole_0,k9_relat_1(sK2,k1_wellord1(sK0,sK3)))
    | ~ spl6_226 ),
    inference(superposition,[],[f198,f2108])).

fof(f198,plain,(
    ! [X0] : r1_tarski(sK5(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f102,f89])).

fof(f2109,plain,
    ( spl6_226
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_224 ),
    inference(avatar_split_clause,[],[f2094,f2035,f280,f267,f2107])).

fof(f267,plain,
    ( spl6_32
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f280,plain,
    ( spl6_34
  <=> k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f2035,plain,
    ( spl6_224
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_224])])).

fof(f2094,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_224 ),
    inference(forward_demodulation,[],[f2089,f281])).

fof(f281,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f280])).

fof(f2089,plain,
    ( sK5(k1_zfmisc_1(k1_xboole_0)) = sK5(k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ spl6_32
    | ~ spl6_224 ),
    inference(resolution,[],[f2036,f271])).

fof(f271,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK5(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl6_32 ),
    inference(resolution,[],[f268,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t8_boole)).

fof(f268,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f267])).

fof(f2036,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3)))))
    | ~ spl6_224 ),
    inference(avatar_component_clause,[],[f2035])).

fof(f2086,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_76
    | ~ spl6_186
    | spl6_199 ),
    inference(avatar_contradiction_clause,[],[f2085])).

fof(f2085,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_76
    | ~ spl6_186
    | ~ spl6_199 ),
    inference(subsumption_resolution,[],[f2084,f114])).

fof(f2084,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_76
    | ~ spl6_186
    | ~ spl6_199 ),
    inference(subsumption_resolution,[],[f2083,f121])).

fof(f2083,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_14
    | ~ spl6_76
    | ~ spl6_186
    | ~ spl6_199 ),
    inference(subsumption_resolution,[],[f2082,f142])).

fof(f2082,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_76
    | ~ spl6_186
    | ~ spl6_199 ),
    inference(subsumption_resolution,[],[f2081,f589])).

fof(f2081,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_186
    | ~ spl6_199 ),
    inference(subsumption_resolution,[],[f2080,f163])).

fof(f2080,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_186
    | ~ spl6_199 ),
    inference(resolution,[],[f1564,f1650])).

fof(f1650,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_xboole_0))
    | ~ spl6_199 ),
    inference(avatar_component_clause,[],[f1649])).

fof(f1649,plain,
    ( spl6_199
  <=> ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_199])])).

fof(f1564,plain,
    ( ! [X2,X3] :
        ( r4_wellord1(k2_wellord1(X2,k1_wellord1(sK0,sK3)),k2_wellord1(X3,k1_xboole_0))
        | ~ r3_wellord1(X2,X3,sK2)
        | ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(X2))
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_186 ),
    inference(subsumption_resolution,[],[f1563,f128])).

fof(f1563,plain,
    ( ! [X2,X3] :
        ( r4_wellord1(k2_wellord1(X2,k1_wellord1(sK0,sK3)),k2_wellord1(X3,k1_xboole_0))
        | ~ r3_wellord1(X2,X3,sK2)
        | ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(X2))
        | ~ v2_wellord1(X2)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl6_6
    | ~ spl6_186 ),
    inference(subsumption_resolution,[],[f1560,f135])).

fof(f1560,plain,
    ( ! [X2,X3] :
        ( r4_wellord1(k2_wellord1(X2,k1_wellord1(sK0,sK3)),k2_wellord1(X3,k1_xboole_0))
        | ~ r3_wellord1(X2,X3,sK2)
        | ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(X2))
        | ~ v2_wellord1(X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl6_186 ),
    inference(superposition,[],[f98,f1553])).

fof(f1553,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_wellord1(sK0,sK3))
    | ~ spl6_186 ),
    inference(avatar_component_clause,[],[f1552])).

fof(f1552,plain,
    ( spl6_186
  <=> k1_xboole_0 = k9_relat_1(sK2,k1_wellord1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_186])])).

fof(f2037,plain,
    ( spl6_222
    | spl6_184
    | spl6_224
    | ~ spl6_88
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f1487,f1471,f621,f2035,f1536,f2029])).

fof(f2029,plain,
    ( spl6_222
  <=> m1_subset_1(sK5(sK5(k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3))))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_222])])).

fof(f1536,plain,
    ( spl6_184
  <=> v1_xboole_0(k9_relat_1(sK2,k1_wellord1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_184])])).

fof(f621,plain,
    ( spl6_88
  <=> ! [X7] : r2_hidden(k1_wellord1(sK1,X7),k1_zfmisc_1(k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f1471,plain,
    ( spl6_174
  <=> k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK3)) = k9_relat_1(sK2,k1_wellord1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_174])])).

fof(f1487,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3)))))
    | v1_xboole_0(k9_relat_1(sK2,k1_wellord1(sK0,sK3)))
    | m1_subset_1(sK5(sK5(k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3))))),k3_relat_1(sK1))
    | ~ spl6_88
    | ~ spl6_174 ),
    inference(forward_demodulation,[],[f1486,f1472])).

fof(f1472,plain,
    ( k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK3)) = k9_relat_1(sK2,k1_wellord1(sK0,sK3))
    | ~ spl6_174 ),
    inference(avatar_component_clause,[],[f1471])).

fof(f1486,plain,
    ( v1_xboole_0(k9_relat_1(sK2,k1_wellord1(sK0,sK3)))
    | m1_subset_1(sK5(sK5(k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3))))),k3_relat_1(sK1))
    | v1_xboole_0(sK5(k1_zfmisc_1(k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK3)))))
    | ~ spl6_88
    | ~ spl6_174 ),
    inference(forward_demodulation,[],[f1480,f1472])).

fof(f1480,plain,
    ( m1_subset_1(sK5(sK5(k1_zfmisc_1(k9_relat_1(sK2,k1_wellord1(sK0,sK3))))),k3_relat_1(sK1))
    | v1_xboole_0(k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK3)))
    | v1_xboole_0(sK5(k1_zfmisc_1(k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK3)))))
    | ~ spl6_88
    | ~ spl6_174 ),
    inference(superposition,[],[f1424,f1472])).

fof(f1424,plain,
    ( ! [X5] :
        ( m1_subset_1(sK5(sK5(k1_zfmisc_1(k1_wellord1(sK1,X5)))),k3_relat_1(sK1))
        | v1_xboole_0(k1_wellord1(sK1,X5))
        | v1_xboole_0(sK5(k1_zfmisc_1(k1_wellord1(sK1,X5)))) )
    | ~ spl6_88 ),
    inference(resolution,[],[f1414,f647])).

fof(f647,plain,
    ( ! [X1] : r1_tarski(k1_wellord1(sK1,X1),k3_relat_1(sK1))
    | ~ spl6_88 ),
    inference(resolution,[],[f622,f199])).

fof(f622,plain,
    ( ! [X7] : r2_hidden(k1_wellord1(sK1,X7),k1_zfmisc_1(k3_relat_1(sK1)))
    | ~ spl6_88 ),
    inference(avatar_component_clause,[],[f621])).

fof(f1414,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X0)
      | m1_subset_1(sK5(sK5(k1_zfmisc_1(X0))),X1)
      | v1_xboole_0(sK5(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f500,f103])).

fof(f500,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | v1_xboole_0(sK5(k1_zfmisc_1(X1)))
      | v1_xboole_0(X1)
      | m1_subset_1(sK5(sK5(k1_zfmisc_1(X1))),X2) ) ),
    inference(resolution,[],[f387,f106])).

fof(f1995,plain,
    ( ~ spl6_221
    | ~ spl6_214 ),
    inference(avatar_split_clause,[],[f1987,f1961,f1993])).

fof(f1993,plain,
    ( spl6_221
  <=> ~ r2_hidden(k3_relat_1(sK1),sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_221])])).

fof(f1961,plain,
    ( spl6_214
  <=> r2_hidden(sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_214])])).

fof(f1987,plain,
    ( ~ r2_hidden(k3_relat_1(sK1),sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0))))
    | ~ spl6_214 ),
    inference(resolution,[],[f1962,f100])).

fof(f1962,plain,
    ( r2_hidden(sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0))),k3_relat_1(sK1))
    | ~ spl6_214 ),
    inference(avatar_component_clause,[],[f1961])).

fof(f1983,plain,
    ( spl6_115
    | spl6_219 ),
    inference(avatar_contradiction_clause,[],[f1982])).

fof(f1982,plain,
    ( $false
    | ~ spl6_115
    | ~ spl6_219 ),
    inference(subsumption_resolution,[],[f1981,f749])).

fof(f1981,plain,
    ( v1_xboole_0(k3_relat_1(sK0))
    | ~ spl6_219 ),
    inference(resolution,[],[f1979,f202])).

fof(f1979,plain,
    ( ~ r2_hidden(sK5(k3_relat_1(sK0)),k3_relat_1(sK0))
    | ~ spl6_219 ),
    inference(avatar_component_clause,[],[f1978])).

fof(f1978,plain,
    ( spl6_219
  <=> ~ r2_hidden(sK5(k3_relat_1(sK0)),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_219])])).

fof(f1980,plain,
    ( ~ spl6_219
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | spl6_215 ),
    inference(avatar_split_clause,[],[f1973,f1964,f162,f134,f127,f120,f113,f1978])).

fof(f1964,plain,
    ( spl6_215
  <=> ~ r2_hidden(sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_215])])).

fof(f1973,plain,
    ( ~ r2_hidden(sK5(k3_relat_1(sK0)),k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_215 ),
    inference(resolution,[],[f1965,f1377])).

fof(f1377,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,sK1,sK2,X0),k3_relat_1(sK1))
        | ~ r2_hidden(X0,k3_relat_1(sK0)) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1376,f114])).

fof(f1376,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK0))
        | r2_hidden(sK4(sK0,sK1,sK2,X0),k3_relat_1(sK1))
        | ~ v1_relat_1(sK0) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1375,f121])).

fof(f1375,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK0))
        | r2_hidden(sK4(sK0,sK1,sK2,X0),k3_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK0) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(resolution,[],[f521,f163])).

fof(f521,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_wellord1(X1,X2,sK2)
        | ~ r2_hidden(X0,k3_relat_1(X1))
        | r2_hidden(sK4(X1,X2,sK2,X0),k3_relat_1(X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f520,f128])).

fof(f520,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(X1))
        | ~ r3_wellord1(X1,X2,sK2)
        | r2_hidden(sK4(X1,X2,sK2,X0),k3_relat_1(X2))
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f87,f135])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_wellord1(X1,sK4(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3))
                    & r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f67])).

fof(f67,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3))
          & r2_hidden(X4,k3_relat_1(X1)) )
     => ( k1_wellord1(X1,sK4(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3))
        & r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3))
                      & r2_hidden(X4,k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3))
                      & r2_hidden(X4,k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ! [X3] :
                    ~ ( ! [X4] :
                          ~ ( k1_wellord1(X1,X4) = k9_relat_1(X2,k1_wellord1(X0,X3))
                            & r2_hidden(X4,k3_relat_1(X1)) )
                      & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t60_wellord1)).

fof(f1965,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0))),k3_relat_1(sK1))
    | ~ spl6_215 ),
    inference(avatar_component_clause,[],[f1964])).

fof(f1972,plain,
    ( ~ spl6_215
    | ~ spl6_217
    | ~ spl6_200 ),
    inference(avatar_split_clause,[],[f1673,f1670,f1970,f1964])).

fof(f1970,plain,
    ( spl6_217
  <=> ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_217])])).

fof(f1670,plain,
    ( spl6_200
  <=> k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0)))) = k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_200])])).

fof(f1673,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))))
    | ~ r2_hidden(sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0))),k3_relat_1(sK1))
    | ~ spl6_200 ),
    inference(superposition,[],[f79,f1671])).

fof(f1671,plain,
    ( k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0)))) = k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))
    | ~ spl6_200 ),
    inference(avatar_component_clause,[],[f1670])).

fof(f79,plain,(
    ! [X4] :
      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
      | ~ r2_hidden(X4,k3_relat_1(sK1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,
    ( ! [X4] :
        ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
        | ~ r2_hidden(X4,k3_relat_1(sK1)) )
    & r2_hidden(sK3,k3_relat_1(sK0))
    & r3_wellord1(sK0,sK1,sK2)
    & v2_wellord1(sK0)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f65,f64,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                        | ~ r2_hidden(X4,k3_relat_1(X1)) )
                    & r2_hidden(X3,k3_relat_1(X0)) )
                & r3_wellord1(X0,X1,X2)
                & v2_wellord1(X0)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(sK0)) )
              & r3_wellord1(sK0,X1,X2)
              & v2_wellord1(sK0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
                    | ~ r2_hidden(X4,k3_relat_1(sK1)) )
                & r2_hidden(X3,k3_relat_1(X0)) )
            & r3_wellord1(X0,sK1,X2)
            & v2_wellord1(X0)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                  | ~ r2_hidden(X4,k3_relat_1(X1)) )
              & r2_hidden(X3,k3_relat_1(X0)) )
          & r3_wellord1(X0,X1,X2)
          & v2_wellord1(X0)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                | ~ r2_hidden(X4,k3_relat_1(X1)) )
            & r2_hidden(X3,k3_relat_1(X0)) )
        & r3_wellord1(X0,X1,sK2)
        & v2_wellord1(X0)
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
              | ~ r2_hidden(X4,k3_relat_1(X1)) )
          & r2_hidden(X3,k3_relat_1(X0)) )
     => ( ! [X4] :
            ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,sK3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
            | ~ r2_hidden(X4,k3_relat_1(X1)) )
        & r2_hidden(sK3,k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => ! [X3] :
                      ~ ( ! [X4] :
                            ~ ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                              & r2_hidden(X4,k3_relat_1(X1)) )
                        & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => ! [X3] :
                    ~ ( ! [X4] :
                          ~ ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                            & r2_hidden(X4,k3_relat_1(X1)) )
                      & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t61_wellord1)).

fof(f1781,plain,
    ( ~ spl6_213
    | spl6_210
    | ~ spl6_124
    | ~ spl6_200 ),
    inference(avatar_split_clause,[],[f1684,f1670,f866,f1764,f1776])).

fof(f1776,plain,
    ( spl6_213
  <=> ~ r2_hidden(k3_relat_1(sK1),sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_213])])).

fof(f1764,plain,
    ( spl6_210
  <=> v1_xboole_0(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_210])])).

fof(f866,plain,
    ( spl6_124
  <=> ! [X0] :
        ( r2_hidden(sK5(k1_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_xboole_0(k1_wellord1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).

fof(f1684,plain,
    ( v1_xboole_0(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0)))))
    | ~ r2_hidden(k3_relat_1(sK1),sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))))
    | ~ spl6_124
    | ~ spl6_200 ),
    inference(forward_demodulation,[],[f1678,f1671])).

fof(f1678,plain,
    ( ~ r2_hidden(k3_relat_1(sK1),sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))))
    | v1_xboole_0(k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0)))))
    | ~ spl6_124
    | ~ spl6_200 ),
    inference(superposition,[],[f945,f1671])).

fof(f945,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k3_relat_1(sK1),sK5(k1_wellord1(sK1,X4)))
        | v1_xboole_0(k1_wellord1(sK1,X4)) )
    | ~ spl6_124 ),
    inference(resolution,[],[f867,f100])).

fof(f867,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_xboole_0(k1_wellord1(sK1,X0)) )
    | ~ spl6_124 ),
    inference(avatar_component_clause,[],[f866])).

fof(f1778,plain,
    ( ~ spl6_213
    | ~ spl6_208 ),
    inference(avatar_split_clause,[],[f1770,f1758,f1776])).

fof(f1758,plain,
    ( spl6_208
  <=> r2_hidden(sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_208])])).

fof(f1770,plain,
    ( ~ r2_hidden(k3_relat_1(sK1),sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))))
    | ~ spl6_208 ),
    inference(resolution,[],[f1759,f100])).

fof(f1759,plain,
    ( r2_hidden(sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))),k3_relat_1(sK1))
    | ~ spl6_208 ),
    inference(avatar_component_clause,[],[f1758])).

fof(f1766,plain,
    ( spl6_208
    | spl6_210
    | ~ spl6_124
    | ~ spl6_200 ),
    inference(avatar_split_clause,[],[f1683,f1670,f866,f1764,f1758])).

fof(f1683,plain,
    ( v1_xboole_0(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0)))))
    | r2_hidden(sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))),k3_relat_1(sK1))
    | ~ spl6_124
    | ~ spl6_200 ),
    inference(forward_demodulation,[],[f1677,f1671])).

fof(f1677,plain,
    ( r2_hidden(sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))),k3_relat_1(sK1))
    | v1_xboole_0(k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0)))))
    | ~ spl6_124
    | ~ spl6_200 ),
    inference(superposition,[],[f867,f1671])).

fof(f1727,plain,
    ( ~ spl6_207
    | ~ spl6_88
    | ~ spl6_200 ),
    inference(avatar_split_clause,[],[f1676,f1670,f621,f1725])).

fof(f1725,plain,
    ( spl6_207
  <=> ~ r2_hidden(k1_zfmisc_1(k3_relat_1(sK1)),k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_207])])).

fof(f1676,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k3_relat_1(sK1)),k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0)))))
    | ~ spl6_88
    | ~ spl6_200 ),
    inference(superposition,[],[f651,f1671])).

fof(f651,plain,
    ( ! [X4] : ~ r2_hidden(k1_zfmisc_1(k3_relat_1(sK1)),k1_wellord1(sK1,X4))
    | ~ spl6_88 ),
    inference(resolution,[],[f622,f100])).

fof(f1712,plain,
    ( spl6_204
    | ~ spl6_88
    | ~ spl6_200 ),
    inference(avatar_split_clause,[],[f1674,f1670,f621,f1710])).

fof(f1710,plain,
    ( spl6_204
  <=> r2_hidden(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0)))),k1_zfmisc_1(k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_204])])).

fof(f1674,plain,
    ( r2_hidden(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0)))),k1_zfmisc_1(k3_relat_1(sK1)))
    | ~ spl6_88
    | ~ spl6_200 ),
    inference(superposition,[],[f622,f1671])).

fof(f1697,plain,
    ( spl6_202
    | ~ spl6_88
    | ~ spl6_200 ),
    inference(avatar_split_clause,[],[f1675,f1670,f621,f1695])).

fof(f1695,plain,
    ( spl6_202
  <=> r1_tarski(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0)))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_202])])).

fof(f1675,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0)))),k3_relat_1(sK1))
    | ~ spl6_88
    | ~ spl6_200 ),
    inference(superposition,[],[f647,f1671])).

fof(f1672,plain,
    ( spl6_200
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | spl6_115 ),
    inference(avatar_split_clause,[],[f1465,f748,f162,f134,f127,f120,f113,f1670])).

fof(f1465,plain,
    ( k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0)))) = k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_115 ),
    inference(subsumption_resolution,[],[f1463,f749])).

fof(f1463,plain,
    ( k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK5(k3_relat_1(sK0)))) = k9_relat_1(sK2,k1_wellord1(sK0,sK5(k3_relat_1(sK0))))
    | v1_xboole_0(k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(resolution,[],[f1447,f202])).

fof(f1447,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK0))
        | k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0)) = k9_relat_1(sK2,k1_wellord1(sK0,X0)) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1446,f114])).

fof(f1446,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK0))
        | k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0)) = k9_relat_1(sK2,k1_wellord1(sK0,X0))
        | ~ v1_relat_1(sK0) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f1445,f121])).

fof(f1445,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK0))
        | k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0)) = k9_relat_1(sK2,k1_wellord1(sK0,X0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(sK0) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(resolution,[],[f737,f163])).

fof(f737,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_wellord1(X1,X2,sK2)
        | ~ r2_hidden(X0,k3_relat_1(X1))
        | k1_wellord1(X2,sK4(X1,X2,sK2,X0)) = k9_relat_1(sK2,k1_wellord1(X1,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f736,f128])).

fof(f736,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(X1))
        | ~ r3_wellord1(X1,X2,sK2)
        | k1_wellord1(X2,sK4(X1,X2,sK2,X0)) = k9_relat_1(sK2,k1_wellord1(X1,X0))
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f88,f135])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | k1_wellord1(X1,sK4(X0,X1,X2,X3)) = k9_relat_1(X2,k1_wellord1(X0,X3))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1651,plain,
    ( ~ spl6_199
    | ~ spl6_186
    | spl6_197 ),
    inference(avatar_split_clause,[],[f1644,f1638,f1552,f1649])).

fof(f1644,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_xboole_0))
    | ~ spl6_186
    | ~ spl6_197 ),
    inference(forward_demodulation,[],[f1639,f1553])).

fof(f1643,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16
    | spl6_195 ),
    inference(avatar_contradiction_clause,[],[f1642])).

fof(f1642,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_195 ),
    inference(subsumption_resolution,[],[f1641,f170])).

fof(f170,plain,
    ( r2_hidden(sK3,k3_relat_1(sK0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl6_16
  <=> r2_hidden(sK3,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f1641,plain,
    ( ~ r2_hidden(sK3,k3_relat_1(sK0))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_195 ),
    inference(resolution,[],[f1633,f1377])).

fof(f1633,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK2,sK3),k3_relat_1(sK1))
    | ~ spl6_195 ),
    inference(avatar_component_clause,[],[f1632])).

fof(f1632,plain,
    ( spl6_195
  <=> ~ r2_hidden(sK4(sK0,sK1,sK2,sK3),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_195])])).

fof(f1640,plain,
    ( ~ spl6_195
    | ~ spl6_197
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f1474,f1471,f1638,f1632])).

fof(f1474,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ r2_hidden(sK4(sK0,sK1,sK2,sK3),k3_relat_1(sK1))
    | ~ spl6_174 ),
    inference(superposition,[],[f79,f1472])).

fof(f1603,plain,
    ( ~ spl6_193
    | spl6_184
    | ~ spl6_124
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f1485,f1471,f866,f1536,f1601])).

fof(f1601,plain,
    ( spl6_193
  <=> ~ r2_hidden(k3_relat_1(sK1),sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_193])])).

fof(f1485,plain,
    ( v1_xboole_0(k9_relat_1(sK2,k1_wellord1(sK0,sK3)))
    | ~ r2_hidden(k3_relat_1(sK1),sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ spl6_124
    | ~ spl6_174 ),
    inference(forward_demodulation,[],[f1479,f1472])).

fof(f1479,plain,
    ( ~ r2_hidden(k3_relat_1(sK1),sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | v1_xboole_0(k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK3)))
    | ~ spl6_124
    | ~ spl6_174 ),
    inference(superposition,[],[f945,f1472])).

fof(f1586,plain,
    ( spl6_190
    | ~ spl6_178
    | ~ spl6_186 ),
    inference(avatar_split_clause,[],[f1557,f1552,f1506,f1584])).

fof(f1506,plain,
    ( spl6_178
  <=> r2_hidden(k9_relat_1(sK2,k1_wellord1(sK0,sK3)),k1_zfmisc_1(k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_178])])).

fof(f1557,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k3_relat_1(sK1)))
    | ~ spl6_178
    | ~ spl6_186 ),
    inference(superposition,[],[f1507,f1553])).

fof(f1507,plain,
    ( r2_hidden(k9_relat_1(sK2,k1_wellord1(sK0,sK3)),k1_zfmisc_1(k3_relat_1(sK1)))
    | ~ spl6_178 ),
    inference(avatar_component_clause,[],[f1506])).

fof(f1571,plain,
    ( spl6_188
    | ~ spl6_176
    | ~ spl6_186 ),
    inference(avatar_split_clause,[],[f1558,f1552,f1496,f1569])).

fof(f1569,plain,
    ( spl6_188
  <=> r1_tarski(k1_xboole_0,k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_188])])).

fof(f1496,plain,
    ( spl6_176
  <=> r1_tarski(k9_relat_1(sK2,k1_wellord1(sK0,sK3)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_176])])).

fof(f1558,plain,
    ( r1_tarski(k1_xboole_0,k3_relat_1(sK1))
    | ~ spl6_176
    | ~ spl6_186 ),
    inference(superposition,[],[f1497,f1553])).

fof(f1497,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_wellord1(sK0,sK3)),k3_relat_1(sK1))
    | ~ spl6_176 ),
    inference(avatar_component_clause,[],[f1496])).

fof(f1554,plain,
    ( spl6_186
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_184 ),
    inference(avatar_split_clause,[],[f1544,f1536,f280,f267,f1552])).

fof(f1544,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_wellord1(sK0,sK3))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_184 ),
    inference(forward_demodulation,[],[f1539,f281])).

fof(f1539,plain,
    ( k9_relat_1(sK2,k1_wellord1(sK0,sK3)) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_184 ),
    inference(resolution,[],[f1537,f271])).

fof(f1537,plain,
    ( v1_xboole_0(k9_relat_1(sK2,k1_wellord1(sK0,sK3)))
    | ~ spl6_184 ),
    inference(avatar_component_clause,[],[f1536])).

fof(f1538,plain,
    ( spl6_182
    | spl6_184
    | ~ spl6_124
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f1484,f1471,f866,f1536,f1530])).

fof(f1530,plain,
    ( spl6_182
  <=> r2_hidden(sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK3))),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_182])])).

fof(f1484,plain,
    ( v1_xboole_0(k9_relat_1(sK2,k1_wellord1(sK0,sK3)))
    | r2_hidden(sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK3))),k3_relat_1(sK1))
    | ~ spl6_124
    | ~ spl6_174 ),
    inference(forward_demodulation,[],[f1478,f1472])).

fof(f1478,plain,
    ( r2_hidden(sK5(k9_relat_1(sK2,k1_wellord1(sK0,sK3))),k3_relat_1(sK1))
    | v1_xboole_0(k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK3)))
    | ~ spl6_124
    | ~ spl6_174 ),
    inference(superposition,[],[f867,f1472])).

fof(f1523,plain,
    ( ~ spl6_181
    | ~ spl6_88
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f1477,f1471,f621,f1521])).

fof(f1521,plain,
    ( spl6_181
  <=> ~ r2_hidden(k1_zfmisc_1(k3_relat_1(sK1)),k9_relat_1(sK2,k1_wellord1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_181])])).

fof(f1477,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k3_relat_1(sK1)),k9_relat_1(sK2,k1_wellord1(sK0,sK3)))
    | ~ spl6_88
    | ~ spl6_174 ),
    inference(superposition,[],[f651,f1472])).

fof(f1508,plain,
    ( spl6_178
    | ~ spl6_88
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f1475,f1471,f621,f1506])).

fof(f1475,plain,
    ( r2_hidden(k9_relat_1(sK2,k1_wellord1(sK0,sK3)),k1_zfmisc_1(k3_relat_1(sK1)))
    | ~ spl6_88
    | ~ spl6_174 ),
    inference(superposition,[],[f622,f1472])).

fof(f1498,plain,
    ( spl6_176
    | ~ spl6_88
    | ~ spl6_174 ),
    inference(avatar_split_clause,[],[f1476,f1471,f621,f1496])).

fof(f1476,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_wellord1(sK0,sK3)),k3_relat_1(sK1))
    | ~ spl6_88
    | ~ spl6_174 ),
    inference(superposition,[],[f647,f1472])).

fof(f1473,plain,
    ( spl6_174
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f1460,f169,f162,f134,f127,f120,f113,f1471])).

fof(f1460,plain,
    ( k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK3)) = k9_relat_1(sK2,k1_wellord1(sK0,sK3))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(resolution,[],[f1447,f170])).

fof(f1396,plain,
    ( spl6_50
    | spl6_52
    | spl6_40
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f505,f148,f314,f412,f406])).

fof(f406,plain,
    ( spl6_50
  <=> v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f412,plain,
    ( spl6_52
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f314,plain,
    ( spl6_40
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f148,plain,
    ( spl6_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f505,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl6_10 ),
    inference(resolution,[],[f387,f262])).

fof(f262,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X1) )
    | ~ spl6_10 ),
    inference(resolution,[],[f210,f101])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f208,f202])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f107,f149])).

fof(f149,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f148])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t5_subset)).

fof(f1395,plain,
    ( spl6_68
    | spl6_172
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f1230,f444,f1393,f532])).

fof(f532,plain,
    ( spl6_68
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f1393,plain,
    ( spl6_172
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_172])])).

fof(f444,plain,
    ( spl6_56
  <=> k1_xboole_0 = sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f1230,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) )
    | ~ spl6_56 ),
    inference(superposition,[],[f335,f445])).

fof(f445,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f444])).

fof(f1382,plain,
    ( spl6_40
    | spl6_170
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f363,f280,f1380,f314])).

fof(f1380,plain,
    ( spl6_170
  <=> ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_170])])).

fof(f363,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0))
        | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_34 ),
    inference(superposition,[],[f335,f281])).

fof(f1378,plain,
    ( spl6_124
    | spl6_126
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f917,f621,f872,f866])).

fof(f872,plain,
    ( spl6_126
  <=> v1_xboole_0(k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_126])])).

fof(f917,plain,
    ( ! [X0] :
        ( v1_xboole_0(k3_relat_1(sK1))
        | r2_hidden(sK5(k1_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_xboole_0(k1_wellord1(sK1,X0)) )
    | ~ spl6_88 ),
    inference(resolution,[],[f647,f389])).

fof(f389,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | v1_xboole_0(X4)
      | r2_hidden(sK5(X3),X4)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f362,f103])).

fof(f1374,plain,
    ( spl6_112
    | spl6_114
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f810,f563,f751,f745])).

fof(f745,plain,
    ( spl6_112
  <=> ! [X0] :
        ( r2_hidden(sK5(k1_wellord1(sK0,X0)),k3_relat_1(sK0))
        | v1_xboole_0(k1_wellord1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_112])])).

fof(f751,plain,
    ( spl6_114
  <=> v1_xboole_0(k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).

fof(f810,plain,
    ( ! [X0] :
        ( v1_xboole_0(k3_relat_1(sK0))
        | r2_hidden(sK5(k1_wellord1(sK0,X0)),k3_relat_1(sK0))
        | v1_xboole_0(k1_wellord1(sK0,X0)) )
    | ~ spl6_76 ),
    inference(resolution,[],[f589,f389])).

fof(f1347,plain,
    ( ~ spl6_169
    | spl6_165 ),
    inference(avatar_split_clause,[],[f1333,f1329,f1345])).

fof(f1345,plain,
    ( spl6_169
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_169])])).

fof(f1329,plain,
    ( spl6_165
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_165])])).

fof(f1333,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_165 ),
    inference(resolution,[],[f1330,f101])).

fof(f1330,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_165 ),
    inference(avatar_component_clause,[],[f1329])).

fof(f1340,plain,
    ( ~ spl6_167
    | spl6_165 ),
    inference(avatar_split_clause,[],[f1332,f1329,f1338])).

fof(f1338,plain,
    ( spl6_167
  <=> ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_167])])).

fof(f1332,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl6_165 ),
    inference(resolution,[],[f1330,f103])).

fof(f1331,plain,
    ( ~ spl6_165
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_162 ),
    inference(avatar_split_clause,[],[f1324,f1313,f280,f267,f1329])).

fof(f1324,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_162 ),
    inference(forward_demodulation,[],[f1320,f281])).

fof(f1320,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK5(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_32
    | ~ spl6_162 ),
    inference(resolution,[],[f1314,f270])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK5(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl6_32 ),
    inference(resolution,[],[f268,f107])).

fof(f1315,plain,
    ( spl6_68
    | spl6_162
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f1232,f444,f1313,f532])).

fof(f1232,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_56 ),
    inference(superposition,[],[f202,f445])).

fof(f1299,plain,
    ( spl6_160
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f1287,f532,f280,f267,f1297])).

fof(f1297,plain,
    ( spl6_160
  <=> k1_xboole_0 = k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_160])])).

fof(f1287,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f1282,f281])).

fof(f1282,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_68 ),
    inference(resolution,[],[f533,f271])).

fof(f533,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f532])).

fof(f1291,plain,
    ( spl6_72
    | ~ spl6_70 ),
    inference(avatar_split_clause,[],[f1275,f535,f544])).

fof(f544,plain,
    ( spl6_72
  <=> r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f535,plain,
    ( spl6_70
  <=> m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f1275,plain,
    ( r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_70 ),
    inference(resolution,[],[f536,f102])).

fof(f536,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f535])).

fof(f1281,plain,
    ( spl6_68
    | ~ spl6_70
    | spl6_75 ),
    inference(avatar_split_clause,[],[f1280,f554,f535,f532])).

fof(f554,plain,
    ( spl6_75
  <=> ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f1280,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_70
    | ~ spl6_75 ),
    inference(subsumption_resolution,[],[f1276,f555])).

fof(f555,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f554])).

fof(f1276,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_70 ),
    inference(resolution,[],[f536,f99])).

fof(f1271,plain,
    ( spl6_40
    | spl6_42
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f359,f293,f320,f314])).

fof(f293,plain,
    ( spl6_36
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f359,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_36 ),
    inference(resolution,[],[f204,f294])).

fof(f294,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f293])).

fof(f204,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,X3)
      | r2_hidden(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f99,f103])).

fof(f1257,plain,
    ( ~ spl6_45
    | ~ spl6_10
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_100
    | ~ spl6_142 ),
    inference(avatar_split_clause,[],[f1135,f1004,f679,f280,f267,f148,f331])).

fof(f331,plain,
    ( spl6_45
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f679,plain,
    ( spl6_100
  <=> ! [X8] : r2_hidden(k1_wellord1(sK2,X8),k1_zfmisc_1(k3_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f1004,plain,
    ( spl6_142
  <=> v1_xboole_0(k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_142])])).

fof(f1135,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_100
    | ~ spl6_142 ),
    inference(forward_demodulation,[],[f708,f1062])).

fof(f1062,plain,
    ( k3_relat_1(sK2) = k1_xboole_0
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_142 ),
    inference(forward_demodulation,[],[f1057,f281])).

fof(f1057,plain,
    ( k3_relat_1(sK2) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_142 ),
    inference(resolution,[],[f1005,f271])).

fof(f1005,plain,
    ( v1_xboole_0(k3_relat_1(sK2))
    | ~ spl6_142 ),
    inference(avatar_component_clause,[],[f1004])).

fof(f708,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK2)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_100 ),
    inference(resolution,[],[f680,f208])).

fof(f680,plain,
    ( ! [X8] : r2_hidden(k1_wellord1(sK2,X8),k1_zfmisc_1(k3_relat_1(sK2)))
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f679])).

fof(f1251,plain,
    ( spl6_158
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f1233,f444,f1249])).

fof(f1249,plain,
    ( spl6_158
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_158])])).

fof(f1233,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_56 ),
    inference(superposition,[],[f89,f445])).

fof(f1240,plain,
    ( spl6_156
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f1229,f444,f1238])).

fof(f1238,plain,
    ( spl6_156
  <=> r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_156])])).

fof(f1229,plain,
    ( r1_tarski(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_56 ),
    inference(superposition,[],[f198,f445])).

fof(f1195,plain,
    ( ~ spl6_155
    | spl6_55
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f1139,f444,f425,f1193])).

fof(f1193,plain,
    ( spl6_155
  <=> k1_xboole_0 != sK5(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_155])])).

fof(f425,plain,
    ( spl6_55
  <=> k1_xboole_0 != sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f1139,plain,
    ( k1_xboole_0 != sK5(k1_xboole_0)
    | ~ spl6_55
    | ~ spl6_56 ),
    inference(forward_demodulation,[],[f426,f445])).

fof(f426,plain,
    ( k1_xboole_0 != sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f425])).

fof(f1159,plain,
    ( spl6_152
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_142 ),
    inference(avatar_split_clause,[],[f1062,f1004,f280,f267,f1157])).

fof(f1157,plain,
    ( spl6_152
  <=> k3_relat_1(sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_152])])).

fof(f1141,plain,
    ( ~ spl6_151
    | spl6_51
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f1140,f444,f403,f1129])).

fof(f403,plain,
    ( spl6_51
  <=> ~ v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f1140,plain,
    ( ~ v1_xboole_0(sK5(k1_xboole_0))
    | ~ spl6_51
    | ~ spl6_56 ),
    inference(forward_demodulation,[],[f404,f445])).

fof(f404,plain,
    ( ~ v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f403])).

fof(f1134,plain,
    ( spl6_150
    | ~ spl6_32
    | ~ spl6_122 ),
    inference(avatar_split_clause,[],[f1070,f840,f267,f1132])).

fof(f1132,plain,
    ( spl6_150
  <=> v1_xboole_0(sK5(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_150])])).

fof(f840,plain,
    ( spl6_122
  <=> k1_xboole_0 = k1_zfmisc_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).

fof(f1070,plain,
    ( v1_xboole_0(sK5(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_122 ),
    inference(superposition,[],[f268,f841])).

fof(f841,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl6_122 ),
    inference(avatar_component_clause,[],[f840])).

fof(f1126,plain,
    ( ~ spl6_149
    | ~ spl6_122
    | spl6_135 ),
    inference(avatar_split_clause,[],[f1087,f954,f840,f1124])).

fof(f1124,plain,
    ( spl6_149
  <=> ~ m1_subset_1(k3_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_149])])).

fof(f954,plain,
    ( spl6_135
  <=> ~ m1_subset_1(k3_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_135])])).

fof(f1087,plain,
    ( ~ m1_subset_1(k3_relat_1(sK1),k1_xboole_0)
    | ~ spl6_122
    | ~ spl6_135 ),
    inference(superposition,[],[f955,f841])).

fof(f955,plain,
    ( ~ m1_subset_1(k3_relat_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_135 ),
    inference(avatar_component_clause,[],[f954])).

fof(f1118,plain,
    ( ~ spl6_147
    | spl6_21
    | ~ spl6_122 ),
    inference(avatar_split_clause,[],[f1067,f840,f215,f1116])).

fof(f1116,plain,
    ( spl6_147
  <=> ~ m1_subset_1(k3_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_147])])).

fof(f215,plain,
    ( spl6_21
  <=> ~ m1_subset_1(k3_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f1067,plain,
    ( ~ m1_subset_1(k3_relat_1(sK0),k1_xboole_0)
    | ~ spl6_21
    | ~ spl6_122 ),
    inference(superposition,[],[f216,f841])).

fof(f216,plain,
    ( ~ m1_subset_1(k3_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f215])).

fof(f1054,plain,
    ( spl6_144
    | ~ spl6_104 ),
    inference(avatar_split_clause,[],[f1023,f701,f1052])).

fof(f1052,plain,
    ( spl6_144
  <=> r1_tarski(sK5(k1_xboole_0),k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_144])])).

fof(f701,plain,
    ( spl6_104
  <=> k1_xboole_0 = k1_zfmisc_1(k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f1023,plain,
    ( r1_tarski(sK5(k1_xboole_0),k3_relat_1(sK2))
    | ~ spl6_104 ),
    inference(superposition,[],[f198,f702])).

fof(f702,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k3_relat_1(sK2))
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f701])).

fof(f1006,plain,
    ( spl6_140
    | spl6_142
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f704,f679,f1004,f998])).

fof(f998,plain,
    ( spl6_140
  <=> ! [X0] :
        ( r2_hidden(sK5(k1_wellord1(sK2,X0)),k3_relat_1(sK2))
        | v1_xboole_0(k1_wellord1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_140])])).

fof(f704,plain,
    ( ! [X0] :
        ( v1_xboole_0(k3_relat_1(sK2))
        | r2_hidden(sK5(k1_wellord1(sK2,X0)),k3_relat_1(sK2))
        | v1_xboole_0(k1_wellord1(sK2,X0)) )
    | ~ spl6_100 ),
    inference(resolution,[],[f680,f390])).

fof(f390,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k1_zfmisc_1(X6))
      | v1_xboole_0(X6)
      | r2_hidden(sK5(X5),X6)
      | v1_xboole_0(X5) ) ),
    inference(resolution,[],[f362,f101])).

fof(f972,plain,
    ( ~ spl6_139
    | spl6_135 ),
    inference(avatar_split_clause,[],[f958,f954,f970])).

fof(f970,plain,
    ( spl6_139
  <=> ~ r2_hidden(k3_relat_1(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_139])])).

fof(f958,plain,
    ( ~ r2_hidden(k3_relat_1(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_135 ),
    inference(resolution,[],[f955,f101])).

fof(f965,plain,
    ( ~ spl6_137
    | spl6_135 ),
    inference(avatar_split_clause,[],[f957,f954,f963])).

fof(f963,plain,
    ( spl6_137
  <=> ~ r1_tarski(k3_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_137])])).

fof(f957,plain,
    ( ~ r1_tarski(k3_relat_1(sK1),k1_xboole_0)
    | ~ spl6_135 ),
    inference(resolution,[],[f955,f103])).

fof(f956,plain,
    ( spl6_132
    | ~ spl6_135
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_124 ),
    inference(avatar_split_clause,[],[f946,f866,f280,f267,f954,f948])).

fof(f948,plain,
    ( spl6_132
  <=> ! [X0] : v1_xboole_0(k1_wellord1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).

fof(f946,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_relat_1(sK1),k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(k1_wellord1(sK1,X0)) )
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_124 ),
    inference(forward_demodulation,[],[f942,f281])).

fof(f942,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_wellord1(sK1,X0))
        | ~ m1_subset_1(k3_relat_1(sK1),k1_zfmisc_1(sK5(k1_zfmisc_1(k1_xboole_0)))) )
    | ~ spl6_32
    | ~ spl6_124 ),
    inference(resolution,[],[f867,f270])).

fof(f932,plain,
    ( spl6_130
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_126 ),
    inference(avatar_split_clause,[],[f913,f872,f280,f267,f930])).

fof(f930,plain,
    ( spl6_130
  <=> k3_relat_1(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).

fof(f913,plain,
    ( k3_relat_1(sK1) = k1_xboole_0
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_126 ),
    inference(forward_demodulation,[],[f908,f281])).

fof(f908,plain,
    ( k3_relat_1(sK1) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_126 ),
    inference(resolution,[],[f873,f271])).

fof(f873,plain,
    ( v1_xboole_0(k3_relat_1(sK1))
    | ~ spl6_126 ),
    inference(avatar_component_clause,[],[f872])).

fof(f907,plain,
    ( spl6_128
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f878,f643,f905])).

fof(f905,plain,
    ( spl6_128
  <=> r1_tarski(sK5(k1_xboole_0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).

fof(f643,plain,
    ( spl6_92
  <=> k1_xboole_0 = k1_zfmisc_1(k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f878,plain,
    ( r1_tarski(sK5(k1_xboole_0),k3_relat_1(sK1))
    | ~ spl6_92 ),
    inference(superposition,[],[f198,f644])).

fof(f644,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k3_relat_1(sK1))
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f643])).

fof(f874,plain,
    ( spl6_124
    | spl6_126
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f646,f621,f872,f866])).

fof(f646,plain,
    ( ! [X0] :
        ( v1_xboole_0(k3_relat_1(sK1))
        | r2_hidden(sK5(k1_wellord1(sK1,X0)),k3_relat_1(sK1))
        | v1_xboole_0(k1_wellord1(sK1,X0)) )
    | ~ spl6_88 ),
    inference(resolution,[],[f622,f390])).

fof(f855,plain,
    ( spl6_40
    | spl6_42
    | spl6_53
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f754,f428,f409,f320,f314])).

fof(f409,plain,
    ( spl6_53
  <=> ~ v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f428,plain,
    ( spl6_54
  <=> k1_xboole_0 = sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f754,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_53
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f510,f410])).

fof(f410,plain,
    ( ~ v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f409])).

fof(f510,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_54 ),
    inference(superposition,[],[f387,f429])).

fof(f429,plain,
    ( k1_xboole_0 = sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f428])).

fof(f852,plain,
    ( ~ spl6_83
    | ~ spl6_10
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f823,f563,f148,f601])).

fof(f601,plain,
    ( spl6_83
  <=> ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f823,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_76 ),
    inference(resolution,[],[f564,f208])).

fof(f842,plain,
    ( spl6_122
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f761,f314,f280,f267,f840])).

fof(f761,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k1_xboole_0)
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f756,f281])).

fof(f756,plain,
    ( k1_zfmisc_1(k1_xboole_0) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_40 ),
    inference(resolution,[],[f315,f271])).

fof(f315,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f314])).

fof(f834,plain,
    ( ~ spl6_121
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_40
    | spl6_83 ),
    inference(avatar_split_clause,[],[f799,f601,f314,f280,f267,f832])).

fof(f799,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK0)),k1_xboole_0)
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_40
    | ~ spl6_83 ),
    inference(forward_demodulation,[],[f602,f761])).

fof(f602,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f601])).

fof(f818,plain,
    ( spl6_118
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_114 ),
    inference(avatar_split_clause,[],[f806,f751,f280,f267,f816])).

fof(f816,plain,
    ( spl6_118
  <=> k3_relat_1(sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f806,plain,
    ( k3_relat_1(sK0) = k1_xboole_0
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_114 ),
    inference(forward_demodulation,[],[f801,f281])).

fof(f801,plain,
    ( k3_relat_1(sK0) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_114 ),
    inference(resolution,[],[f752,f271])).

fof(f752,plain,
    ( v1_xboole_0(k3_relat_1(sK0))
    | ~ spl6_114 ),
    inference(avatar_component_clause,[],[f751])).

fof(f798,plain,
    ( spl6_116
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f768,f585,f796])).

fof(f796,plain,
    ( spl6_116
  <=> r1_tarski(sK5(k1_xboole_0),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f768,plain,
    ( r1_tarski(sK5(k1_xboole_0),k3_relat_1(sK0))
    | ~ spl6_80 ),
    inference(superposition,[],[f198,f586])).

fof(f753,plain,
    ( spl6_112
    | spl6_114
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f588,f563,f751,f745])).

fof(f588,plain,
    ( ! [X0] :
        ( v1_xboole_0(k3_relat_1(sK0))
        | r2_hidden(sK5(k1_wellord1(sK0,X0)),k3_relat_1(sK0))
        | v1_xboole_0(k1_wellord1(sK0,X0)) )
    | ~ spl6_76 ),
    inference(resolution,[],[f564,f390])).

fof(f735,plain,
    ( ~ spl6_111
    | spl6_107 ),
    inference(avatar_split_clause,[],[f721,f717,f733])).

fof(f733,plain,
    ( spl6_111
  <=> ~ r2_hidden(k1_zfmisc_1(k3_relat_1(sK2)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f717,plain,
    ( spl6_107
  <=> ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK2)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f721,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k3_relat_1(sK2)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_107 ),
    inference(resolution,[],[f718,f101])).

fof(f718,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK2)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_107 ),
    inference(avatar_component_clause,[],[f717])).

fof(f728,plain,
    ( ~ spl6_109
    | spl6_107 ),
    inference(avatar_split_clause,[],[f720,f717,f726])).

fof(f726,plain,
    ( spl6_109
  <=> ~ r1_tarski(k1_zfmisc_1(k3_relat_1(sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_109])])).

fof(f720,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_relat_1(sK2)),k1_xboole_0)
    | ~ spl6_107 ),
    inference(resolution,[],[f718,f103])).

fof(f719,plain,
    ( ~ spl6_107
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f710,f679,f280,f267,f717])).

fof(f710,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK2)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_100 ),
    inference(forward_demodulation,[],[f706,f281])).

fof(f706,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK2)),k1_zfmisc_1(sK5(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_32
    | ~ spl6_100 ),
    inference(resolution,[],[f680,f270])).

fof(f703,plain,
    ( spl6_104
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_102 ),
    inference(avatar_split_clause,[],[f693,f685,f280,f267,f701])).

fof(f685,plain,
    ( spl6_102
  <=> v1_xboole_0(k1_zfmisc_1(k3_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f693,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k3_relat_1(sK2))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_102 ),
    inference(forward_demodulation,[],[f688,f281])).

fof(f688,plain,
    ( k1_zfmisc_1(k3_relat_1(sK2)) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_102 ),
    inference(resolution,[],[f686,f271])).

fof(f686,plain,
    ( v1_xboole_0(k1_zfmisc_1(k3_relat_1(sK2)))
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f685])).

fof(f687,plain,
    ( spl6_100
    | spl6_102
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f561,f127,f685,f679])).

fof(f561,plain,
    ( ! [X8] :
        ( v1_xboole_0(k1_zfmisc_1(k3_relat_1(sK2)))
        | r2_hidden(k1_wellord1(sK2,X8),k1_zfmisc_1(k3_relat_1(sK2))) )
    | ~ spl6_4 ),
    inference(resolution,[],[f358,f128])).

fof(f358,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X1)
      | v1_xboole_0(k1_zfmisc_1(k3_relat_1(X1)))
      | r2_hidden(k1_wellord1(X1,X2),k1_zfmisc_1(k3_relat_1(X1))) ) ),
    inference(resolution,[],[f204,f96])).

fof(f677,plain,
    ( ~ spl6_99
    | spl6_95 ),
    inference(avatar_split_clause,[],[f663,f659,f675])).

fof(f675,plain,
    ( spl6_99
  <=> ~ r2_hidden(k1_zfmisc_1(k3_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f659,plain,
    ( spl6_95
  <=> ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f663,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k3_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_95 ),
    inference(resolution,[],[f660,f101])).

fof(f660,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_95 ),
    inference(avatar_component_clause,[],[f659])).

fof(f670,plain,
    ( ~ spl6_97
    | spl6_95 ),
    inference(avatar_split_clause,[],[f662,f659,f668])).

fof(f668,plain,
    ( spl6_97
  <=> ~ r1_tarski(k1_zfmisc_1(k3_relat_1(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f662,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_relat_1(sK1)),k1_xboole_0)
    | ~ spl6_95 ),
    inference(resolution,[],[f660,f103])).

fof(f661,plain,
    ( ~ spl6_95
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_88 ),
    inference(avatar_split_clause,[],[f652,f621,f280,f267,f659])).

fof(f652,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK1)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_88 ),
    inference(forward_demodulation,[],[f648,f281])).

fof(f648,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK1)),k1_zfmisc_1(sK5(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_32
    | ~ spl6_88 ),
    inference(resolution,[],[f622,f270])).

fof(f645,plain,
    ( spl6_92
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_90 ),
    inference(avatar_split_clause,[],[f635,f627,f280,f267,f643])).

fof(f627,plain,
    ( spl6_90
  <=> v1_xboole_0(k1_zfmisc_1(k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f635,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k3_relat_1(sK1))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_90 ),
    inference(forward_demodulation,[],[f630,f281])).

fof(f630,plain,
    ( k1_zfmisc_1(k3_relat_1(sK1)) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_90 ),
    inference(resolution,[],[f628,f271])).

fof(f628,plain,
    ( v1_xboole_0(k1_zfmisc_1(k3_relat_1(sK1)))
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f627])).

fof(f629,plain,
    ( spl6_88
    | spl6_90
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f560,f120,f627,f621])).

fof(f560,plain,
    ( ! [X7] :
        ( v1_xboole_0(k1_zfmisc_1(k3_relat_1(sK1)))
        | r2_hidden(k1_wellord1(sK1,X7),k1_zfmisc_1(k3_relat_1(sK1))) )
    | ~ spl6_2 ),
    inference(resolution,[],[f358,f121])).

fof(f619,plain,
    ( ~ spl6_87
    | spl6_83 ),
    inference(avatar_split_clause,[],[f605,f601,f617])).

fof(f617,plain,
    ( spl6_87
  <=> ~ r2_hidden(k1_zfmisc_1(k3_relat_1(sK0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f605,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k3_relat_1(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_83 ),
    inference(resolution,[],[f602,f101])).

fof(f612,plain,
    ( ~ spl6_85
    | spl6_83 ),
    inference(avatar_split_clause,[],[f604,f601,f610])).

fof(f610,plain,
    ( spl6_85
  <=> ~ r1_tarski(k1_zfmisc_1(k3_relat_1(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f604,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_relat_1(sK0)),k1_xboole_0)
    | ~ spl6_83 ),
    inference(resolution,[],[f602,f103])).

fof(f603,plain,
    ( ~ spl6_83
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f594,f563,f280,f267,f601])).

fof(f594,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_76 ),
    inference(forward_demodulation,[],[f590,f281])).

fof(f590,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k3_relat_1(sK0)),k1_zfmisc_1(sK5(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_32
    | ~ spl6_76 ),
    inference(resolution,[],[f564,f270])).

fof(f587,plain,
    ( spl6_80
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f577,f569,f280,f267,f585])).

fof(f569,plain,
    ( spl6_78
  <=> v1_xboole_0(k1_zfmisc_1(k3_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f577,plain,
    ( k1_xboole_0 = k1_zfmisc_1(k3_relat_1(sK0))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_78 ),
    inference(forward_demodulation,[],[f572,f281])).

fof(f572,plain,
    ( k1_zfmisc_1(k3_relat_1(sK0)) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_78 ),
    inference(resolution,[],[f570,f271])).

fof(f570,plain,
    ( v1_xboole_0(k1_zfmisc_1(k3_relat_1(sK0)))
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f569])).

fof(f571,plain,
    ( spl6_76
    | spl6_78
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f559,f113,f569,f563])).

fof(f559,plain,
    ( ! [X6] :
        ( v1_xboole_0(k1_zfmisc_1(k3_relat_1(sK0)))
        | r2_hidden(k1_wellord1(sK0,X6),k1_zfmisc_1(k3_relat_1(sK0))) )
    | ~ spl6_0 ),
    inference(resolution,[],[f358,f114])).

fof(f556,plain,
    ( ~ spl6_75
    | spl6_71 ),
    inference(avatar_split_clause,[],[f542,f538,f554])).

fof(f538,plain,
    ( spl6_71
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f542,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_71 ),
    inference(resolution,[],[f539,f101])).

fof(f539,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_71 ),
    inference(avatar_component_clause,[],[f538])).

fof(f549,plain,
    ( ~ spl6_73
    | spl6_71 ),
    inference(avatar_split_clause,[],[f541,f538,f547])).

fof(f547,plain,
    ( spl6_73
  <=> ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f541,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_71 ),
    inference(resolution,[],[f539,f103])).

fof(f540,plain,
    ( spl6_68
    | ~ spl6_71
    | spl6_63 ),
    inference(avatar_split_clause,[],[f482,f479,f538,f532])).

fof(f479,plain,
    ( spl6_63
  <=> ~ m1_subset_1(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f482,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_63 ),
    inference(resolution,[],[f480,f335])).

fof(f480,plain,
    ( ~ m1_subset_1(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f479])).

fof(f498,plain,
    ( ~ spl6_67
    | spl6_63 ),
    inference(avatar_split_clause,[],[f484,f479,f496])).

fof(f496,plain,
    ( spl6_67
  <=> ~ r2_hidden(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f484,plain,
    ( ~ r2_hidden(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_63 ),
    inference(resolution,[],[f480,f101])).

fof(f491,plain,
    ( ~ spl6_65
    | spl6_63 ),
    inference(avatar_split_clause,[],[f483,f479,f489])).

fof(f489,plain,
    ( spl6_65
  <=> ~ r1_tarski(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f483,plain,
    ( ~ r1_tarski(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_xboole_0)
    | ~ spl6_63 ),
    inference(resolution,[],[f480,f103])).

fof(f481,plain,
    ( ~ spl6_63
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f474,f467,f280,f267,f479])).

fof(f467,plain,
    ( spl6_60
  <=> r2_hidden(k1_xboole_0,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f474,plain,
    ( ~ m1_subset_1(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_60 ),
    inference(forward_demodulation,[],[f470,f281])).

fof(f470,plain,
    ( ~ m1_subset_1(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))),k1_zfmisc_1(sK5(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_32
    | ~ spl6_60 ),
    inference(resolution,[],[f468,f270])).

fof(f468,plain,
    ( r2_hidden(k1_xboole_0,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f467])).

fof(f469,plain,
    ( spl6_60
    | spl6_53
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f454,f428,f409,f467])).

fof(f454,plain,
    ( r2_hidden(k1_xboole_0,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_53
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f451,f410])).

fof(f451,plain,
    ( r2_hidden(k1_xboole_0,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_54 ),
    inference(superposition,[],[f202,f429])).

fof(f461,plain,
    ( spl6_58
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f452,f428,f459])).

fof(f459,plain,
    ( spl6_58
  <=> m1_subset_1(k1_xboole_0,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f452,plain,
    ( m1_subset_1(k1_xboole_0,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_54 ),
    inference(superposition,[],[f89,f429])).

fof(f446,plain,
    ( spl6_56
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f436,f412,f280,f267,f444])).

fof(f436,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_52 ),
    inference(forward_demodulation,[],[f431,f281])).

fof(f431,plain,
    ( sK5(k1_zfmisc_1(k1_xboole_0)) = sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_32
    | ~ spl6_52 ),
    inference(resolution,[],[f413,f271])).

fof(f413,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f412])).

fof(f430,plain,
    ( spl6_54
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f420,f406,f280,f267,f428])).

fof(f420,plain,
    ( k1_xboole_0 = sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f415,f281])).

fof(f415,plain,
    ( sK5(k1_zfmisc_1(k1_xboole_0)) = sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl6_32
    | ~ spl6_50 ),
    inference(resolution,[],[f407,f271])).

fof(f407,plain,
    ( v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f406])).

fof(f414,plain,
    ( spl6_50
    | spl6_52
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f380,f148,f412,f406])).

fof(f380,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | v1_xboole_0(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl6_10 ),
    inference(resolution,[],[f361,f89])).

fof(f361,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
        | v1_xboole_0(X2)
        | v1_xboole_0(sK5(X2)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f335,f210])).

fof(f352,plain,
    ( ~ spl6_49
    | spl6_45 ),
    inference(avatar_split_clause,[],[f338,f331,f350])).

fof(f350,plain,
    ( spl6_49
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f338,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_45 ),
    inference(resolution,[],[f332,f101])).

fof(f332,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f331])).

fof(f345,plain,
    ( ~ spl6_47
    | spl6_45 ),
    inference(avatar_split_clause,[],[f337,f331,f343])).

fof(f343,plain,
    ( spl6_47
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f337,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_45 ),
    inference(resolution,[],[f332,f103])).

fof(f333,plain,
    ( ~ spl6_45
    | ~ spl6_10
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f325,f320,f148,f331])).

fof(f325,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_42 ),
    inference(resolution,[],[f321,f208])).

fof(f322,plain,
    ( spl6_40
    | spl6_42
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f287,f280,f320,f314])).

fof(f287,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_34 ),
    inference(superposition,[],[f202,f281])).

fof(f303,plain,
    ( spl6_38
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f288,f280,f301])).

fof(f301,plain,
    ( spl6_38
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f288,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_34 ),
    inference(superposition,[],[f89,f281])).

fof(f295,plain,
    ( spl6_36
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f285,f280,f293])).

fof(f285,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_34 ),
    inference(superposition,[],[f198,f281])).

fof(f282,plain,
    ( spl6_34
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f273,f267,f280])).

fof(f273,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_32 ),
    inference(resolution,[],[f268,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',t6_boole)).

fof(f269,plain,
    ( spl6_32
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f260,f148,f267])).

fof(f260,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl6_10 ),
    inference(resolution,[],[f210,f89])).

fof(f259,plain,
    ( spl6_30
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f231,f127,f257])).

fof(f257,plain,
    ( spl6_30
  <=> k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f231,plain,
    ( k3_relat_1(sK2) = k2_xboole_0(k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl6_4 ),
    inference(resolution,[],[f85,f128])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',d6_relat_1)).

fof(f252,plain,
    ( spl6_28
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f230,f120,f250])).

fof(f250,plain,
    ( spl6_28
  <=> k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f230,plain,
    ( k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))
    | ~ spl6_2 ),
    inference(resolution,[],[f85,f121])).

fof(f245,plain,
    ( spl6_26
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f229,f113,f243])).

fof(f243,plain,
    ( spl6_26
  <=> k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f229,plain,
    ( k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl6_0 ),
    inference(resolution,[],[f85,f114])).

fof(f238,plain,
    ( ~ spl6_25
    | spl6_21 ),
    inference(avatar_split_clause,[],[f219,f215,f236])).

fof(f236,plain,
    ( spl6_25
  <=> ~ r2_hidden(k3_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f219,plain,
    ( ~ r2_hidden(k3_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_21 ),
    inference(resolution,[],[f216,f101])).

fof(f226,plain,
    ( ~ spl6_23
    | spl6_21 ),
    inference(avatar_split_clause,[],[f218,f215,f224])).

fof(f224,plain,
    ( spl6_23
  <=> ~ r1_tarski(k3_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f218,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k1_xboole_0)
    | ~ spl6_21 ),
    inference(resolution,[],[f216,f103])).

fof(f217,plain,
    ( ~ spl6_21
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f209,f169,f148,f215])).

fof(f209,plain,
    ( ~ m1_subset_1(k3_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(resolution,[],[f208,f170])).

fof(f181,plain,
    ( ~ spl6_19
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f174,f169,f179])).

fof(f179,plain,
    ( spl6_19
  <=> ~ r2_hidden(k3_relat_1(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f174,plain,
    ( ~ r2_hidden(k3_relat_1(sK0),sK3)
    | ~ spl6_16 ),
    inference(resolution,[],[f100,f170])).

fof(f171,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f78,f169])).

fof(f78,plain,(
    r2_hidden(sK3,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

fof(f164,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f77,f162])).

fof(f77,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f157,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f81,f155])).

fof(f155,plain,
    ( spl6_12
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f81,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',d2_xboole_0)).

fof(f150,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f108,f148])).

fof(f108,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f80,f81])).

fof(f80,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t61_wellord1.p',dt_o_0_0_xboole_0)).

fof(f143,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f76,f141])).

fof(f76,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f136,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f75,f134])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f129,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f74,f127])).

fof(f74,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f122,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f73,f120])).

fof(f73,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f115,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f72,f113])).

fof(f72,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f66])).
%------------------------------------------------------------------------------
