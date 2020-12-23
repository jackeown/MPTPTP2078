%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:20 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  298 ( 614 expanded)
%              Number of leaves         :   67 ( 270 expanded)
%              Depth                    :   14
%              Number of atoms          :  952 (1910 expanded)
%              Number of equality atoms :  174 ( 362 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2424,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f137,f155,f194,f196,f213,f229,f251,f417,f470,f674,f706,f758,f766,f850,f869,f884,f937,f979,f1102,f1113,f1185,f1192,f1340,f1411,f1489,f1509,f1519,f1610,f1631,f1644,f1667,f1671,f2134,f2205,f2267,f2327,f2353,f2362,f2401,f2410])).

fof(f2410,plain,
    ( ~ spl8_1
    | spl8_3
    | ~ spl8_13
    | ~ spl8_80
    | ~ spl8_88
    | ~ spl8_100
    | ~ spl8_189
    | ~ spl8_297 ),
    inference(avatar_contradiction_clause,[],[f2409])).

fof(f2409,plain,
    ( $false
    | ~ spl8_1
    | spl8_3
    | ~ spl8_13
    | ~ spl8_80
    | ~ spl8_88
    | ~ spl8_100
    | ~ spl8_189
    | ~ spl8_297 ),
    inference(subsumption_resolution,[],[f2408,f2399])).

fof(f2399,plain,
    ( ! [X0] : sP1(X0,k2_funct_1(k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_13
    | ~ spl8_88
    | ~ spl8_189
    | ~ spl8_297 ),
    inference(subsumption_resolution,[],[f2369,f64])).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2369,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | sP1(X0,k2_funct_1(k1_xboole_0)) )
    | ~ spl8_1
    | ~ spl8_13
    | ~ spl8_88
    | ~ spl8_189
    | ~ spl8_297 ),
    inference(backward_demodulation,[],[f2109,f2361])).

fof(f2361,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_297 ),
    inference(avatar_component_clause,[],[f2359])).

fof(f2359,plain,
    ( spl8_297
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_297])])).

fof(f2109,plain,
    ( ! [X0] :
        ( sP1(X0,k2_funct_1(k1_xboole_0))
        | ~ r1_tarski(k1_relat_1(k1_xboole_0),X0) )
    | ~ spl8_1
    | ~ spl8_13
    | ~ spl8_88
    | ~ spl8_189 ),
    inference(forward_demodulation,[],[f1734,f1662])).

fof(f1662,plain,
    ( k1_xboole_0 = sK7
    | ~ spl8_189 ),
    inference(avatar_component_clause,[],[f1660])).

fof(f1660,plain,
    ( spl8_189
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_189])])).

fof(f1734,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k1_xboole_0),X0)
        | sP1(X0,k2_funct_1(sK7)) )
    | ~ spl8_1
    | ~ spl8_13
    | ~ spl8_88
    | ~ spl8_189 ),
    inference(backward_demodulation,[],[f816,f1662])).

fof(f816,plain,
    ( ! [X0] :
        ( sP1(X0,k2_funct_1(sK7))
        | ~ r1_tarski(k1_relat_1(sK7),X0) )
    | ~ spl8_1
    | ~ spl8_13
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f815,f192])).

fof(f192,plain,
    ( v1_relat_1(k2_funct_1(sK7))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl8_13
  <=> v1_relat_1(k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f815,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK7),X0)
        | sP1(X0,k2_funct_1(sK7))
        | ~ v1_relat_1(k2_funct_1(sK7)) )
    | ~ spl8_1
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f812,f102])).

fof(f102,plain,
    ( v1_funct_1(k2_funct_1(sK7))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_1
  <=> v1_funct_1(k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f812,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK7),X0)
        | sP1(X0,k2_funct_1(sK7))
        | ~ v1_funct_1(k2_funct_1(sK7))
        | ~ v1_relat_1(k2_funct_1(sK7)) )
    | ~ spl8_88 ),
    inference(superposition,[],[f77,f757])).

fof(f757,plain,
    ( k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7))
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f755])).

fof(f755,plain,
    ( spl8_88
  <=> k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sP1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f29,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f2408,plain,
    ( ~ sP1(sK5,k2_funct_1(k1_xboole_0))
    | spl8_3
    | ~ spl8_80
    | ~ spl8_100
    | ~ spl8_189 ),
    inference(forward_demodulation,[],[f1237,f1662])).

fof(f1237,plain,
    ( ~ sP1(sK5,k2_funct_1(sK7))
    | spl8_3
    | ~ spl8_80
    | ~ spl8_100 ),
    inference(unit_resulting_resolution,[],[f111,f891])).

fof(f891,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,X0)))
        | ~ sP1(X0,k2_funct_1(sK7)) )
    | ~ spl8_80
    | ~ spl8_100 ),
    inference(backward_demodulation,[],[f731,f879])).

fof(f879,plain,
    ( sK6 = k2_relat_1(sK7)
    | ~ spl8_100 ),
    inference(avatar_component_clause,[],[f877])).

fof(f877,plain,
    ( spl8_100
  <=> sK6 = k2_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_100])])).

fof(f731,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),X0)))
        | ~ sP1(X0,k2_funct_1(sK7)) )
    | ~ spl8_80 ),
    inference(superposition,[],[f76,f673])).

fof(f673,plain,
    ( k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7))
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f671])).

fof(f671,plain,
    ( spl8_80
  <=> k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f111,plain,
    ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_3
  <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f2401,plain,
    ( spl8_256
    | ~ spl8_297 ),
    inference(avatar_contradiction_clause,[],[f2400])).

fof(f2400,plain,
    ( $false
    | spl8_256
    | ~ spl8_297 ),
    inference(subsumption_resolution,[],[f2373,f64])).

fof(f2373,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5)
    | spl8_256
    | ~ spl8_297 ),
    inference(backward_demodulation,[],[f2133,f2361])).

fof(f2133,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK5)
    | spl8_256 ),
    inference(avatar_component_clause,[],[f2131])).

fof(f2131,plain,
    ( spl8_256
  <=> r1_tarski(k1_relat_1(k1_xboole_0),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_256])])).

fof(f2362,plain,
    ( spl8_297
    | ~ spl8_293
    | ~ spl8_296 ),
    inference(avatar_split_clause,[],[f2357,f2350,f2324,f2359])).

fof(f2324,plain,
    ( spl8_293
  <=> k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_293])])).

fof(f2350,plain,
    ( spl8_296
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_296])])).

fof(f2357,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_293
    | ~ spl8_296 ),
    inference(backward_demodulation,[],[f2326,f2352])).

fof(f2352,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_296 ),
    inference(avatar_component_clause,[],[f2350])).

fof(f2326,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_293 ),
    inference(avatar_component_clause,[],[f2324])).

fof(f2353,plain,
    ( spl8_296
    | ~ spl8_270
    | ~ spl8_281 ),
    inference(avatar_split_clause,[],[f2348,f2264,f2202,f2350])).

fof(f2202,plain,
    ( spl8_270
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_270])])).

fof(f2264,plain,
    ( spl8_281
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_281])])).

fof(f2348,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_270
    | ~ spl8_281 ),
    inference(forward_demodulation,[],[f2204,f2266])).

fof(f2266,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_281 ),
    inference(avatar_component_clause,[],[f2264])).

fof(f2204,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl8_270 ),
    inference(avatar_component_clause,[],[f2202])).

fof(f2327,plain,
    ( spl8_293
    | ~ spl8_183
    | ~ spl8_189 ),
    inference(avatar_split_clause,[],[f1797,f1660,f1607,f2324])).

fof(f1607,plain,
    ( spl8_183
  <=> k1_relat_1(sK7) = k10_relat_1(sK7,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_183])])).

fof(f1797,plain,
    ( k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_183
    | ~ spl8_189 ),
    inference(backward_demodulation,[],[f1609,f1662])).

fof(f1609,plain,
    ( k1_relat_1(sK7) = k10_relat_1(sK7,k1_xboole_0)
    | ~ spl8_183 ),
    inference(avatar_component_clause,[],[f1607])).

fof(f2267,plain,
    ( spl8_281
    | ~ spl8_165
    | ~ spl8_189 ),
    inference(avatar_split_clause,[],[f1780,f1660,f1516,f2264])).

fof(f1516,plain,
    ( spl8_165
  <=> k1_xboole_0 = k2_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_165])])).

fof(f1780,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_165
    | ~ spl8_189 ),
    inference(backward_demodulation,[],[f1518,f1662])).

fof(f1518,plain,
    ( k1_xboole_0 = k2_relat_1(sK7)
    | ~ spl8_165 ),
    inference(avatar_component_clause,[],[f1516])).

fof(f2205,plain,
    ( spl8_270
    | ~ spl8_147
    | ~ spl8_189 ),
    inference(avatar_split_clause,[],[f2200,f1660,f1337,f2202])).

fof(f1337,plain,
    ( spl8_147
  <=> k1_xboole_0 = k10_relat_1(sK7,k9_relat_1(sK7,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).

fof(f2200,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl8_147
    | ~ spl8_189 ),
    inference(forward_demodulation,[],[f1756,f1194])).

fof(f1194,plain,(
    ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f1193,f860])).

fof(f860,plain,(
    ! [X0,X1] : k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f164,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f164,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f64,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1193,plain,(
    ! [X0,X1] : k2_relset_1(X0,X1,k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f1164,f1138])).

fof(f1138,plain,(
    ! [X2,X0,X1] : k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(unit_resulting_resolution,[],[f164,f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f1164,plain,(
    ! [X0,X1] : k2_relset_1(X0,X1,k1_xboole_0) = k7_relset_1(X0,X1,k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f164,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f1756,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl8_147
    | ~ spl8_189 ),
    inference(backward_demodulation,[],[f1339,f1662])).

fof(f1339,plain,
    ( k1_xboole_0 = k10_relat_1(sK7,k9_relat_1(sK7,k1_xboole_0))
    | ~ spl8_147 ),
    inference(avatar_component_clause,[],[f1337])).

fof(f2134,plain,
    ( ~ spl8_256
    | spl8_123
    | ~ spl8_189 ),
    inference(avatar_split_clause,[],[f1740,f1660,f1108,f2131])).

fof(f1108,plain,
    ( spl8_123
  <=> r1_tarski(k1_relat_1(sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_123])])).

fof(f1740,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),sK5)
    | spl8_123
    | ~ spl8_189 ),
    inference(backward_demodulation,[],[f1110,f1662])).

fof(f1110,plain,
    ( ~ r1_tarski(k1_relat_1(sK7),sK5)
    | spl8_123 ),
    inference(avatar_component_clause,[],[f1108])).

fof(f1671,plain,
    ( sK6 != k9_relat_1(sK7,sK5)
    | k1_relat_1(sK7) != k10_relat_1(sK7,sK6)
    | k1_xboole_0 != k10_relat_1(sK7,k9_relat_1(sK7,k1_xboole_0))
    | k1_xboole_0 != sK5
    | sK5 = k1_relat_1(sK7) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1667,plain,
    ( spl8_189
    | spl8_190
    | ~ spl8_159
    | ~ spl8_163 ),
    inference(avatar_split_clause,[],[f1658,f1506,f1486,f1664,f1660])).

fof(f1664,plain,
    ( spl8_190
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_190])])).

fof(f1486,plain,
    ( spl8_159
  <=> v1_funct_2(sK7,sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_159])])).

fof(f1506,plain,
    ( spl8_163
  <=> sP4(sK7,k1_xboole_0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_163])])).

fof(f1658,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK7
    | ~ spl8_159
    | ~ spl8_163 ),
    inference(subsumption_resolution,[],[f1657,f1488])).

fof(f1488,plain,
    ( v1_funct_2(sK7,sK5,k1_xboole_0)
    | ~ spl8_159 ),
    inference(avatar_component_clause,[],[f1486])).

fof(f1657,plain,
    ( ~ v1_funct_2(sK7,sK5,k1_xboole_0)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK7
    | ~ spl8_163 ),
    inference(resolution,[],[f1508,f98])).

fof(f98,plain,(
    ! [X2,X0] :
      ( ~ sP4(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f1508,plain,
    ( sP4(sK7,k1_xboole_0,sK5)
    | ~ spl8_163 ),
    inference(avatar_component_clause,[],[f1506])).

fof(f1644,plain,
    ( sK6 != k2_relat_1(sK7)
    | k2_relat_1(sK7) != k1_relat_1(k2_funct_1(sK7))
    | sK5 != k1_relat_1(sK7)
    | k1_relat_1(sK7) != k2_relat_1(k2_funct_1(sK7))
    | v1_funct_2(k2_funct_1(sK7),sK6,sK5)
    | ~ v1_funct_2(k2_funct_1(sK7),k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1631,plain,
    ( sK6 != k2_relat_1(sK7)
    | k2_relat_1(sK7) != k1_relat_1(k2_funct_1(sK7))
    | sK5 != k1_relat_1(sK7)
    | k1_relat_1(sK7) != k2_relat_1(k2_funct_1(sK7))
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1610,plain,
    ( spl8_183
    | ~ spl8_126
    | ~ spl8_132 ),
    inference(avatar_split_clause,[],[f1460,f1189,f1130,f1607])).

fof(f1130,plain,
    ( spl8_126
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).

fof(f1189,plain,
    ( spl8_132
  <=> k1_relat_1(sK7) = k10_relat_1(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_132])])).

fof(f1460,plain,
    ( k1_relat_1(sK7) = k10_relat_1(sK7,k1_xboole_0)
    | ~ spl8_126
    | ~ spl8_132 ),
    inference(backward_demodulation,[],[f1191,f1132])).

fof(f1132,plain,
    ( k1_xboole_0 = sK6
    | ~ spl8_126 ),
    inference(avatar_component_clause,[],[f1130])).

fof(f1191,plain,
    ( k1_relat_1(sK7) = k10_relat_1(sK7,sK6)
    | ~ spl8_132 ),
    inference(avatar_component_clause,[],[f1189])).

fof(f1519,plain,
    ( spl8_165
    | ~ spl8_100
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f1430,f1130,f877,f1516])).

fof(f1430,plain,
    ( k1_xboole_0 = k2_relat_1(sK7)
    | ~ spl8_100
    | ~ spl8_126 ),
    inference(backward_demodulation,[],[f879,f1132])).

fof(f1509,plain,
    ( spl8_163
    | ~ spl8_51
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f1428,f1130,f466,f1506])).

fof(f466,plain,
    ( spl8_51
  <=> sP4(sK7,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f1428,plain,
    ( sP4(sK7,k1_xboole_0,sK5)
    | ~ spl8_51
    | ~ spl8_126 ),
    inference(backward_demodulation,[],[f468,f1132])).

fof(f468,plain,
    ( sP4(sK7,sK6,sK5)
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f466])).

fof(f1489,plain,
    ( spl8_159
    | ~ spl8_7
    | ~ spl8_126 ),
    inference(avatar_split_clause,[],[f1424,f1130,f129,f1486])).

fof(f129,plain,
    ( spl8_7
  <=> v1_funct_2(sK7,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f1424,plain,
    ( v1_funct_2(sK7,sK5,k1_xboole_0)
    | ~ spl8_7
    | ~ spl8_126 ),
    inference(backward_demodulation,[],[f131,f1132])).

fof(f131,plain,
    ( v1_funct_2(sK7,sK5,sK6)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f1411,plain,
    ( ~ spl8_7
    | ~ spl8_44
    | ~ spl8_97
    | spl8_126
    | spl8_149 ),
    inference(avatar_contradiction_clause,[],[f1410])).

fof(f1410,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_44
    | ~ spl8_97
    | spl8_126
    | spl8_149 ),
    inference(subsumption_resolution,[],[f1409,f415])).

fof(f415,plain,
    ( sP3(sK5,sK7,sK6)
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl8_44
  <=> sP3(sK5,sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f1409,plain,
    ( ~ sP3(sK5,sK7,sK6)
    | ~ spl8_7
    | ~ spl8_97
    | spl8_126
    | spl8_149 ),
    inference(subsumption_resolution,[],[f1408,f1143])).

fof(f1143,plain,
    ( ! [X0] : ~ sP2(X0,sK6)
    | spl8_126 ),
    inference(unit_resulting_resolution,[],[f1131,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1131,plain,
    ( k1_xboole_0 != sK6
    | spl8_126 ),
    inference(avatar_component_clause,[],[f1130])).

fof(f1408,plain,
    ( sP2(sK5,sK6)
    | ~ sP3(sK5,sK7,sK6)
    | ~ spl8_7
    | ~ spl8_97
    | spl8_149 ),
    inference(subsumption_resolution,[],[f1407,f131])).

fof(f1407,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | sP2(sK5,sK6)
    | ~ sP3(sK5,sK7,sK6)
    | ~ spl8_97
    | spl8_149 ),
    inference(subsumption_resolution,[],[f1395,f1353])).

fof(f1353,plain,
    ( sK5 != k1_relat_1(sK7)
    | spl8_149 ),
    inference(avatar_component_clause,[],[f1352])).

fof(f1352,plain,
    ( spl8_149
  <=> sK5 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).

fof(f1395,plain,
    ( sK5 = k1_relat_1(sK7)
    | ~ v1_funct_2(sK7,sK5,sK6)
    | sP2(sK5,sK6)
    | ~ sP3(sK5,sK7,sK6)
    | ~ spl8_97 ),
    inference(superposition,[],[f849,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f849,plain,
    ( k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7)
    | ~ spl8_97 ),
    inference(avatar_component_clause,[],[f847])).

fof(f847,plain,
    ( spl8_97
  <=> k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f1340,plain,
    ( spl8_147
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f1329,f150,f134,f119,f1337])).

fof(f119,plain,
    ( spl8_5
  <=> v2_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f134,plain,
    ( spl8_8
  <=> v1_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f150,plain,
    ( spl8_10
  <=> v1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f1329,plain,
    ( k1_xboole_0 = k10_relat_1(sK7,k9_relat_1(sK7,k1_xboole_0))
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f151,f136,f121,f64,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f121,plain,
    ( v2_funct_1(sK7)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f136,plain,
    ( v1_funct_1(sK7)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f151,plain,
    ( v1_relat_1(sK7)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f1192,plain,
    ( spl8_132
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_107
    | ~ spl8_115 ),
    inference(avatar_split_clause,[],[f1187,f976,f934,f150,f134,f119,f1189])).

fof(f934,plain,
    ( spl8_107
  <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_relat_1(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).

fof(f976,plain,
    ( spl8_115
  <=> k1_relat_1(sK7) = k2_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f1187,plain,
    ( k1_relat_1(sK7) = k10_relat_1(sK7,sK6)
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_107
    | ~ spl8_115 ),
    inference(forward_demodulation,[],[f1186,f978])).

fof(f978,plain,
    ( k1_relat_1(sK7) = k2_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7))
    | ~ spl8_115 ),
    inference(avatar_component_clause,[],[f976])).

fof(f1186,plain,
    ( k2_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7)) = k10_relat_1(sK7,sK6)
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_107 ),
    inference(forward_demodulation,[],[f1165,f1142])).

fof(f1142,plain,
    ( ! [X0] : k10_relat_1(sK7,X0) = k7_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7),X0)
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_107 ),
    inference(forward_demodulation,[],[f1139,f1047])).

fof(f1047,plain,
    ( ! [X0] : k10_relat_1(sK7,X0) = k9_relat_1(k2_funct_1(sK7),X0)
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f151,f136,f121,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f1139,plain,
    ( ! [X0] : k9_relat_1(k2_funct_1(sK7),X0) = k7_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7),X0)
    | ~ spl8_107 ),
    inference(unit_resulting_resolution,[],[f936,f95])).

fof(f936,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_relat_1(sK7))))
    | ~ spl8_107 ),
    inference(avatar_component_clause,[],[f934])).

fof(f1165,plain,
    ( k2_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7)) = k7_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7),sK6)
    | ~ spl8_107 ),
    inference(unit_resulting_resolution,[],[f936,f85])).

fof(f1185,plain,
    ( spl8_131
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f1180,f124,f114,f1182])).

fof(f1182,plain,
    ( spl8_131
  <=> sK6 = k9_relat_1(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_131])])).

fof(f114,plain,
    ( spl8_4
  <=> sK6 = k2_relset_1(sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f124,plain,
    ( spl8_6
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f1180,plain,
    ( sK6 = k9_relat_1(sK7,sK5)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f1179,f116])).

fof(f116,plain,
    ( sK6 = k2_relset_1(sK5,sK6,sK7)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1179,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k9_relat_1(sK7,sK5)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f1166,f1140])).

fof(f1140,plain,
    ( ! [X0] : k7_relset_1(sK5,sK6,sK7,X0) = k9_relat_1(sK7,X0)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f126,f95])).

fof(f126,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f1166,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k7_relset_1(sK5,sK6,sK7,sK5)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f126,f85])).

fof(f1113,plain,
    ( ~ spl8_123
    | ~ spl8_1
    | ~ spl8_13
    | ~ spl8_88
    | spl8_122 ),
    inference(avatar_split_clause,[],[f1105,f1098,f755,f191,f101,f1108])).

fof(f1098,plain,
    ( spl8_122
  <=> sP1(sK5,k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).

fof(f1105,plain,
    ( ~ r1_tarski(k1_relat_1(sK7),sK5)
    | ~ spl8_1
    | ~ spl8_13
    | ~ spl8_88
    | spl8_122 ),
    inference(resolution,[],[f1100,f816])).

fof(f1100,plain,
    ( ~ sP1(sK5,k2_funct_1(sK7))
    | spl8_122 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f1102,plain,
    ( ~ spl8_122
    | spl8_2
    | ~ spl8_80
    | ~ spl8_100 ),
    inference(avatar_split_clause,[],[f1096,f877,f671,f105,f1098])).

fof(f105,plain,
    ( spl8_2
  <=> v1_funct_2(k2_funct_1(sK7),sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1096,plain,
    ( ~ sP1(sK5,k2_funct_1(sK7))
    | spl8_2
    | ~ spl8_80
    | ~ spl8_100 ),
    inference(resolution,[],[f892,f107])).

fof(f107,plain,
    ( ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f892,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_funct_1(sK7),sK6,X1)
        | ~ sP1(X1,k2_funct_1(sK7)) )
    | ~ spl8_80
    | ~ spl8_100 ),
    inference(backward_demodulation,[],[f733,f879])).

fof(f733,plain,
    ( ! [X1] :
        ( v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),X1)
        | ~ sP1(X1,k2_funct_1(sK7)) )
    | ~ spl8_80 ),
    inference(superposition,[],[f75,f673])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f979,plain,
    ( spl8_115
    | ~ spl8_98
    | ~ spl8_100 ),
    inference(avatar_split_clause,[],[f974,f877,f866,f976])).

fof(f866,plain,
    ( spl8_98
  <=> k1_relat_1(sK7) = k2_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_98])])).

fof(f974,plain,
    ( k1_relat_1(sK7) = k2_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7))
    | ~ spl8_98
    | ~ spl8_100 ),
    inference(forward_demodulation,[],[f868,f879])).

fof(f868,plain,
    ( k1_relat_1(sK7) = k2_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7))
    | ~ spl8_98 ),
    inference(avatar_component_clause,[],[f866])).

fof(f937,plain,
    ( spl8_107
    | ~ spl8_89
    | ~ spl8_100 ),
    inference(avatar_split_clause,[],[f893,f877,f763,f934])).

fof(f763,plain,
    ( spl8_89
  <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f893,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_relat_1(sK7))))
    | ~ spl8_89
    | ~ spl8_100 ),
    inference(backward_demodulation,[],[f765,f879])).

fof(f765,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7))))
    | ~ spl8_89 ),
    inference(avatar_component_clause,[],[f763])).

fof(f884,plain,
    ( spl8_100
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f883,f124,f114,f877])).

fof(f883,plain,
    ( sK6 = k2_relat_1(sK7)
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f863,f126])).

fof(f863,plain,
    ( sK6 = k2_relat_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ spl8_4 ),
    inference(superposition,[],[f116,f83])).

fof(f869,plain,
    ( spl8_98
    | ~ spl8_88
    | ~ spl8_89 ),
    inference(avatar_split_clause,[],[f864,f763,f755,f866])).

fof(f864,plain,
    ( k1_relat_1(sK7) = k2_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7))
    | ~ spl8_88
    | ~ spl8_89 ),
    inference(forward_demodulation,[],[f861,f757])).

fof(f861,plain,
    ( k2_relat_1(k2_funct_1(sK7)) = k2_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7))
    | ~ spl8_89 ),
    inference(unit_resulting_resolution,[],[f765,f83])).

fof(f850,plain,
    ( spl8_97
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f831,f124,f847])).

fof(f831,plain,
    ( k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f126,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f766,plain,
    ( spl8_89
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_84 ),
    inference(avatar_split_clause,[],[f761,f703,f150,f134,f119,f763])).

fof(f703,plain,
    ( spl8_84
  <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f761,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7))))
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_84 ),
    inference(subsumption_resolution,[],[f760,f151])).

fof(f760,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7))))
    | ~ v1_relat_1(sK7)
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_84 ),
    inference(subsumption_resolution,[],[f759,f136])).

fof(f759,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7))))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_5
    | ~ spl8_84 ),
    inference(subsumption_resolution,[],[f746,f121])).

fof(f746,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7))))
    | ~ v2_funct_1(sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_84 ),
    inference(superposition,[],[f705,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f705,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7)))))
    | ~ spl8_84 ),
    inference(avatar_component_clause,[],[f703])).

fof(f758,plain,
    ( spl8_88
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f744,f150,f134,f119,f755])).

fof(f744,plain,
    ( k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7))
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f151,f136,f121,f72])).

fof(f706,plain,
    ( spl8_84
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f701,f248,f150,f134,f119,f703])).

fof(f248,plain,
    ( spl8_20
  <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f701,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7)))))
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f700,f151])).

fof(f700,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7)))))
    | ~ v1_relat_1(sK7)
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f699,f136])).

fof(f699,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7)))))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_5
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f663,f121])).

fof(f663,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7)))))
    | ~ v2_funct_1(sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl8_20 ),
    inference(superposition,[],[f250,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f250,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7)))))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f248])).

fof(f674,plain,
    ( spl8_80
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f659,f150,f134,f119,f671])).

fof(f659,plain,
    ( k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7))
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f151,f136,f121,f71])).

fof(f470,plain,
    ( spl8_51
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f454,f124,f466])).

fof(f454,plain,
    ( sP4(sK7,sK6,sK5)
    | ~ spl8_6 ),
    inference(resolution,[],[f94,f126])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X2,X1,X0)
        & sP3(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f38,f46,f45,f44])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f417,plain,
    ( spl8_44
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f401,f124,f413])).

fof(f401,plain,
    ( sP3(sK5,sK7,sK6)
    | ~ spl8_6 ),
    inference(resolution,[],[f93,f126])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f251,plain,
    ( spl8_20
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f244,f140,f248])).

fof(f140,plain,
    ( spl8_9
  <=> sP0(k2_funct_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f244,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7)))))
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f141,f67])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f141,plain,
    ( sP0(k2_funct_1(sK7))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f229,plain,
    ( spl8_17
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f222,f140,f226])).

fof(f226,plain,
    ( spl8_17
  <=> v1_funct_2(k2_funct_1(sK7),k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f222,plain,
    ( v1_funct_2(k2_funct_1(sK7),k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7)))
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f141,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f213,plain,
    ( spl8_13
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f204,f150,f134,f191])).

fof(f204,plain,
    ( v1_relat_1(k2_funct_1(sK7))
    | ~ spl8_8
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f136,f151,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f196,plain,
    ( spl8_10
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f179,f124,f150])).

fof(f179,plain,
    ( v1_relat_1(sK7)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f126,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f194,plain,
    ( ~ spl8_13
    | ~ spl8_1
    | spl8_9 ),
    inference(avatar_split_clause,[],[f146,f140,f101,f191])).

fof(f146,plain,
    ( ~ v1_funct_1(k2_funct_1(sK7))
    | ~ v1_relat_1(k2_funct_1(sK7))
    | spl8_9 ),
    inference(resolution,[],[f68,f142])).

fof(f142,plain,
    ( ~ sP0(k2_funct_1(sK7))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f68,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f21,f40])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f155,plain,
    ( ~ spl8_10
    | spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f154,f134,f101,f150])).

fof(f154,plain,
    ( ~ v1_relat_1(sK7)
    | spl8_1
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f148,f136])).

fof(f148,plain,
    ( ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl8_1 ),
    inference(resolution,[],[f70,f103])).

fof(f103,plain,
    ( ~ v1_funct_1(k2_funct_1(sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f137,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f58,f134])).

fof(f58,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
      | ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
      | ~ v1_funct_1(k2_funct_1(sK7)) )
    & sK6 = k2_relset_1(sK5,sK6,sK7)
    & v2_funct_1(sK7)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f19,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
        | ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
        | ~ v1_funct_1(k2_funct_1(sK7)) )
      & sK6 = k2_relset_1(sK5,sK6,sK7)
      & v2_funct_1(sK7)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    spl8_7 ),
    inference(avatar_split_clause,[],[f59,f129])).

fof(f59,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f127,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f60,f124])).

fof(f60,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f49])).

fof(f122,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f61,f119])).

fof(f61,plain,(
    v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f117,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f62,f114])).

fof(f62,plain,(
    sK6 = k2_relset_1(sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f112,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f63,f109,f105,f101])).

fof(f63,plain,
    ( ~ m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_funct_2(k2_funct_1(sK7),sK6,sK5)
    | ~ v1_funct_1(k2_funct_1(sK7)) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:44:53 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.46  % (5436)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (5431)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (5434)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (5426)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (5429)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (5431)Refutation not found, incomplete strategy% (5431)------------------------------
% 0.21/0.50  % (5431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5431)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5431)Memory used [KB]: 1791
% 0.21/0.50  % (5431)Time elapsed: 0.046 s
% 0.21/0.50  % (5431)------------------------------
% 0.21/0.50  % (5431)------------------------------
% 0.21/0.50  % (5419)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (5422)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (5421)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (5430)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.51  % (5423)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.25/0.51  % (5428)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.25/0.52  % (5432)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.25/0.52  % (5418)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.25/0.52  % (5427)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.25/0.52  % (5433)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.25/0.52  % (5424)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.25/0.52  % (5437)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.25/0.52  % (5438)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.25/0.52  % (5419)Refutation not found, incomplete strategy% (5419)------------------------------
% 1.25/0.52  % (5419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (5419)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (5419)Memory used [KB]: 10618
% 1.25/0.52  % (5419)Time elapsed: 0.100 s
% 1.25/0.52  % (5419)------------------------------
% 1.25/0.52  % (5419)------------------------------
% 1.25/0.53  % (5438)Refutation not found, incomplete strategy% (5438)------------------------------
% 1.25/0.53  % (5438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (5438)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (5438)Memory used [KB]: 10618
% 1.25/0.53  % (5438)Time elapsed: 0.112 s
% 1.25/0.53  % (5438)------------------------------
% 1.25/0.53  % (5438)------------------------------
% 1.25/0.53  % (5425)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.25/0.53  % (5420)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.41/0.54  % (5434)Refutation found. Thanks to Tanya!
% 1.41/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.54  % SZS output start Proof for theBenchmark
% 1.41/0.54  fof(f2424,plain,(
% 1.41/0.54    $false),
% 1.41/0.54    inference(avatar_sat_refutation,[],[f112,f117,f122,f127,f132,f137,f155,f194,f196,f213,f229,f251,f417,f470,f674,f706,f758,f766,f850,f869,f884,f937,f979,f1102,f1113,f1185,f1192,f1340,f1411,f1489,f1509,f1519,f1610,f1631,f1644,f1667,f1671,f2134,f2205,f2267,f2327,f2353,f2362,f2401,f2410])).
% 1.41/0.54  fof(f2410,plain,(
% 1.41/0.54    ~spl8_1 | spl8_3 | ~spl8_13 | ~spl8_80 | ~spl8_88 | ~spl8_100 | ~spl8_189 | ~spl8_297),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f2409])).
% 1.41/0.54  fof(f2409,plain,(
% 1.41/0.54    $false | (~spl8_1 | spl8_3 | ~spl8_13 | ~spl8_80 | ~spl8_88 | ~spl8_100 | ~spl8_189 | ~spl8_297)),
% 1.41/0.54    inference(subsumption_resolution,[],[f2408,f2399])).
% 1.41/0.54  fof(f2399,plain,(
% 1.41/0.54    ( ! [X0] : (sP1(X0,k2_funct_1(k1_xboole_0))) ) | (~spl8_1 | ~spl8_13 | ~spl8_88 | ~spl8_189 | ~spl8_297)),
% 1.41/0.54    inference(subsumption_resolution,[],[f2369,f64])).
% 1.41/0.54  fof(f64,plain,(
% 1.41/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f1])).
% 1.41/0.54  fof(f1,axiom,(
% 1.41/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.41/0.54  fof(f2369,plain,(
% 1.41/0.54    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | sP1(X0,k2_funct_1(k1_xboole_0))) ) | (~spl8_1 | ~spl8_13 | ~spl8_88 | ~spl8_189 | ~spl8_297)),
% 1.41/0.54    inference(backward_demodulation,[],[f2109,f2361])).
% 1.41/0.54  fof(f2361,plain,(
% 1.41/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl8_297),
% 1.41/0.54    inference(avatar_component_clause,[],[f2359])).
% 1.41/0.54  fof(f2359,plain,(
% 1.41/0.54    spl8_297 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_297])])).
% 1.41/0.54  fof(f2109,plain,(
% 1.41/0.54    ( ! [X0] : (sP1(X0,k2_funct_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(k1_xboole_0),X0)) ) | (~spl8_1 | ~spl8_13 | ~spl8_88 | ~spl8_189)),
% 1.41/0.54    inference(forward_demodulation,[],[f1734,f1662])).
% 1.41/0.54  fof(f1662,plain,(
% 1.41/0.54    k1_xboole_0 = sK7 | ~spl8_189),
% 1.41/0.54    inference(avatar_component_clause,[],[f1660])).
% 1.41/0.54  fof(f1660,plain,(
% 1.41/0.54    spl8_189 <=> k1_xboole_0 = sK7),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_189])])).
% 1.41/0.54  fof(f1734,plain,(
% 1.41/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_xboole_0),X0) | sP1(X0,k2_funct_1(sK7))) ) | (~spl8_1 | ~spl8_13 | ~spl8_88 | ~spl8_189)),
% 1.41/0.54    inference(backward_demodulation,[],[f816,f1662])).
% 1.41/0.54  fof(f816,plain,(
% 1.41/0.54    ( ! [X0] : (sP1(X0,k2_funct_1(sK7)) | ~r1_tarski(k1_relat_1(sK7),X0)) ) | (~spl8_1 | ~spl8_13 | ~spl8_88)),
% 1.41/0.54    inference(subsumption_resolution,[],[f815,f192])).
% 1.41/0.54  fof(f192,plain,(
% 1.41/0.54    v1_relat_1(k2_funct_1(sK7)) | ~spl8_13),
% 1.41/0.54    inference(avatar_component_clause,[],[f191])).
% 1.41/0.54  fof(f191,plain,(
% 1.41/0.54    spl8_13 <=> v1_relat_1(k2_funct_1(sK7))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.41/0.54  fof(f815,plain,(
% 1.41/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK7),X0) | sP1(X0,k2_funct_1(sK7)) | ~v1_relat_1(k2_funct_1(sK7))) ) | (~spl8_1 | ~spl8_88)),
% 1.41/0.54    inference(subsumption_resolution,[],[f812,f102])).
% 1.41/0.54  fof(f102,plain,(
% 1.41/0.54    v1_funct_1(k2_funct_1(sK7)) | ~spl8_1),
% 1.41/0.54    inference(avatar_component_clause,[],[f101])).
% 1.41/0.54  fof(f101,plain,(
% 1.41/0.54    spl8_1 <=> v1_funct_1(k2_funct_1(sK7))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.41/0.54  fof(f812,plain,(
% 1.41/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK7),X0) | sP1(X0,k2_funct_1(sK7)) | ~v1_funct_1(k2_funct_1(sK7)) | ~v1_relat_1(k2_funct_1(sK7))) ) | ~spl8_88),
% 1.41/0.54    inference(superposition,[],[f77,f757])).
% 1.41/0.54  fof(f757,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7)) | ~spl8_88),
% 1.41/0.54    inference(avatar_component_clause,[],[f755])).
% 1.41/0.54  fof(f755,plain,(
% 1.41/0.54    spl8_88 <=> k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).
% 1.41/0.54  fof(f77,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sP1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f43])).
% 1.41/0.54  fof(f43,plain,(
% 1.41/0.54    ! [X0,X1] : (sP1(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(definition_folding,[],[f29,f42])).
% 1.41/0.54  fof(f42,plain,(
% 1.41/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP1(X0,X1))),
% 1.41/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.41/0.54  fof(f29,plain,(
% 1.41/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(flattening,[],[f28])).
% 1.41/0.54  fof(f28,plain,(
% 1.41/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.41/0.54    inference(ennf_transformation,[],[f15])).
% 1.41/0.54  fof(f15,axiom,(
% 1.41/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.41/0.54  fof(f2408,plain,(
% 1.41/0.54    ~sP1(sK5,k2_funct_1(k1_xboole_0)) | (spl8_3 | ~spl8_80 | ~spl8_100 | ~spl8_189)),
% 1.41/0.54    inference(forward_demodulation,[],[f1237,f1662])).
% 1.41/0.54  fof(f1237,plain,(
% 1.41/0.54    ~sP1(sK5,k2_funct_1(sK7)) | (spl8_3 | ~spl8_80 | ~spl8_100)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f111,f891])).
% 1.41/0.54  fof(f891,plain,(
% 1.41/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,X0))) | ~sP1(X0,k2_funct_1(sK7))) ) | (~spl8_80 | ~spl8_100)),
% 1.41/0.54    inference(backward_demodulation,[],[f731,f879])).
% 1.41/0.54  fof(f879,plain,(
% 1.41/0.54    sK6 = k2_relat_1(sK7) | ~spl8_100),
% 1.41/0.54    inference(avatar_component_clause,[],[f877])).
% 1.41/0.54  fof(f877,plain,(
% 1.41/0.54    spl8_100 <=> sK6 = k2_relat_1(sK7)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_100])])).
% 1.41/0.54  fof(f731,plain,(
% 1.41/0.54    ( ! [X0] : (m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),X0))) | ~sP1(X0,k2_funct_1(sK7))) ) | ~spl8_80),
% 1.41/0.54    inference(superposition,[],[f76,f673])).
% 1.41/0.54  fof(f673,plain,(
% 1.41/0.54    k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7)) | ~spl8_80),
% 1.41/0.54    inference(avatar_component_clause,[],[f671])).
% 1.41/0.54  fof(f671,plain,(
% 1.41/0.54    spl8_80 <=> k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).
% 1.41/0.54  fof(f76,plain,(
% 1.41/0.54    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP1(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f51])).
% 1.41/0.54  fof(f51,plain,(
% 1.41/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP1(X0,X1))),
% 1.41/0.54    inference(nnf_transformation,[],[f42])).
% 1.41/0.54  fof(f111,plain,(
% 1.41/0.54    ~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | spl8_3),
% 1.41/0.54    inference(avatar_component_clause,[],[f109])).
% 1.41/0.54  fof(f109,plain,(
% 1.41/0.54    spl8_3 <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.41/0.54  fof(f2401,plain,(
% 1.41/0.54    spl8_256 | ~spl8_297),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f2400])).
% 1.41/0.54  fof(f2400,plain,(
% 1.41/0.54    $false | (spl8_256 | ~spl8_297)),
% 1.41/0.54    inference(subsumption_resolution,[],[f2373,f64])).
% 1.41/0.54  fof(f2373,plain,(
% 1.41/0.54    ~r1_tarski(k1_xboole_0,sK5) | (spl8_256 | ~spl8_297)),
% 1.41/0.54    inference(backward_demodulation,[],[f2133,f2361])).
% 1.41/0.54  fof(f2133,plain,(
% 1.41/0.54    ~r1_tarski(k1_relat_1(k1_xboole_0),sK5) | spl8_256),
% 1.41/0.54    inference(avatar_component_clause,[],[f2131])).
% 1.41/0.54  fof(f2131,plain,(
% 1.41/0.54    spl8_256 <=> r1_tarski(k1_relat_1(k1_xboole_0),sK5)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_256])])).
% 1.41/0.54  fof(f2362,plain,(
% 1.41/0.54    spl8_297 | ~spl8_293 | ~spl8_296),
% 1.41/0.54    inference(avatar_split_clause,[],[f2357,f2350,f2324,f2359])).
% 1.41/0.54  fof(f2324,plain,(
% 1.41/0.54    spl8_293 <=> k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_293])])).
% 1.41/0.54  fof(f2350,plain,(
% 1.41/0.54    spl8_296 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_296])])).
% 1.41/0.54  fof(f2357,plain,(
% 1.41/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl8_293 | ~spl8_296)),
% 1.41/0.54    inference(backward_demodulation,[],[f2326,f2352])).
% 1.41/0.54  fof(f2352,plain,(
% 1.41/0.54    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~spl8_296),
% 1.41/0.54    inference(avatar_component_clause,[],[f2350])).
% 1.41/0.54  fof(f2326,plain,(
% 1.41/0.54    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~spl8_293),
% 1.41/0.54    inference(avatar_component_clause,[],[f2324])).
% 1.41/0.54  fof(f2353,plain,(
% 1.41/0.54    spl8_296 | ~spl8_270 | ~spl8_281),
% 1.41/0.54    inference(avatar_split_clause,[],[f2348,f2264,f2202,f2350])).
% 1.41/0.54  fof(f2202,plain,(
% 1.41/0.54    spl8_270 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_270])])).
% 1.41/0.54  fof(f2264,plain,(
% 1.41/0.54    spl8_281 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_281])])).
% 1.41/0.54  fof(f2348,plain,(
% 1.41/0.54    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl8_270 | ~spl8_281)),
% 1.41/0.54    inference(forward_demodulation,[],[f2204,f2266])).
% 1.41/0.54  fof(f2266,plain,(
% 1.41/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl8_281),
% 1.41/0.54    inference(avatar_component_clause,[],[f2264])).
% 1.41/0.54  fof(f2204,plain,(
% 1.41/0.54    k1_xboole_0 = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) | ~spl8_270),
% 1.41/0.54    inference(avatar_component_clause,[],[f2202])).
% 1.41/0.54  fof(f2327,plain,(
% 1.41/0.54    spl8_293 | ~spl8_183 | ~spl8_189),
% 1.41/0.54    inference(avatar_split_clause,[],[f1797,f1660,f1607,f2324])).
% 1.41/0.54  fof(f1607,plain,(
% 1.41/0.54    spl8_183 <=> k1_relat_1(sK7) = k10_relat_1(sK7,k1_xboole_0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_183])])).
% 1.41/0.54  fof(f1797,plain,(
% 1.41/0.54    k1_relat_1(k1_xboole_0) = k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl8_183 | ~spl8_189)),
% 1.41/0.54    inference(backward_demodulation,[],[f1609,f1662])).
% 1.41/0.54  fof(f1609,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k10_relat_1(sK7,k1_xboole_0) | ~spl8_183),
% 1.41/0.54    inference(avatar_component_clause,[],[f1607])).
% 1.41/0.54  fof(f2267,plain,(
% 1.41/0.54    spl8_281 | ~spl8_165 | ~spl8_189),
% 1.41/0.54    inference(avatar_split_clause,[],[f1780,f1660,f1516,f2264])).
% 1.41/0.54  fof(f1516,plain,(
% 1.41/0.54    spl8_165 <=> k1_xboole_0 = k2_relat_1(sK7)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_165])])).
% 1.41/0.54  fof(f1780,plain,(
% 1.41/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl8_165 | ~spl8_189)),
% 1.41/0.54    inference(backward_demodulation,[],[f1518,f1662])).
% 1.41/0.54  fof(f1518,plain,(
% 1.41/0.54    k1_xboole_0 = k2_relat_1(sK7) | ~spl8_165),
% 1.41/0.54    inference(avatar_component_clause,[],[f1516])).
% 1.41/0.54  fof(f2205,plain,(
% 1.41/0.54    spl8_270 | ~spl8_147 | ~spl8_189),
% 1.41/0.54    inference(avatar_split_clause,[],[f2200,f1660,f1337,f2202])).
% 1.41/0.54  fof(f1337,plain,(
% 1.41/0.54    spl8_147 <=> k1_xboole_0 = k10_relat_1(sK7,k9_relat_1(sK7,k1_xboole_0))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).
% 1.41/0.54  fof(f2200,plain,(
% 1.41/0.54    k1_xboole_0 = k10_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (~spl8_147 | ~spl8_189)),
% 1.41/0.54    inference(forward_demodulation,[],[f1756,f1194])).
% 1.41/0.54  fof(f1194,plain,(
% 1.41/0.54    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) )),
% 1.41/0.54    inference(forward_demodulation,[],[f1193,f860])).
% 1.41/0.54  fof(f860,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0)) )),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f164,f83])).
% 1.41/0.54  fof(f83,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f34])).
% 1.41/0.54  fof(f34,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f10])).
% 1.41/0.54  fof(f10,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.41/0.54  fof(f164,plain,(
% 1.41/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f64,f80])).
% 1.41/0.54  fof(f80,plain,(
% 1.41/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f52])).
% 1.41/0.54  fof(f52,plain,(
% 1.41/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.41/0.54    inference(nnf_transformation,[],[f2])).
% 1.41/0.54  fof(f2,axiom,(
% 1.41/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.41/0.54  fof(f1193,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k2_relset_1(X0,X1,k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) )),
% 1.41/0.54    inference(forward_demodulation,[],[f1164,f1138])).
% 1.41/0.54  fof(f1138,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2)) )),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f164,f95])).
% 1.41/0.54  fof(f95,plain,(
% 1.41/0.54    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f39])).
% 1.41/0.54  fof(f39,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f11])).
% 1.41/0.54  fof(f11,axiom,(
% 1.41/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.41/0.54  fof(f1164,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k2_relset_1(X0,X1,k1_xboole_0) = k7_relset_1(X0,X1,k1_xboole_0,X0)) )),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f164,f85])).
% 1.41/0.54  fof(f85,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f36])).
% 1.41/0.54  fof(f36,plain,(
% 1.41/0.54    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f12])).
% 1.41/0.54  fof(f12,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 1.41/0.54  fof(f1756,plain,(
% 1.41/0.54    k1_xboole_0 = k10_relat_1(k1_xboole_0,k9_relat_1(k1_xboole_0,k1_xboole_0)) | (~spl8_147 | ~spl8_189)),
% 1.41/0.54    inference(backward_demodulation,[],[f1339,f1662])).
% 1.41/0.54  fof(f1339,plain,(
% 1.41/0.54    k1_xboole_0 = k10_relat_1(sK7,k9_relat_1(sK7,k1_xboole_0)) | ~spl8_147),
% 1.41/0.54    inference(avatar_component_clause,[],[f1337])).
% 1.41/0.54  fof(f2134,plain,(
% 1.41/0.54    ~spl8_256 | spl8_123 | ~spl8_189),
% 1.41/0.54    inference(avatar_split_clause,[],[f1740,f1660,f1108,f2131])).
% 1.41/0.54  fof(f1108,plain,(
% 1.41/0.54    spl8_123 <=> r1_tarski(k1_relat_1(sK7),sK5)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_123])])).
% 1.41/0.54  fof(f1740,plain,(
% 1.41/0.54    ~r1_tarski(k1_relat_1(k1_xboole_0),sK5) | (spl8_123 | ~spl8_189)),
% 1.41/0.54    inference(backward_demodulation,[],[f1110,f1662])).
% 1.41/0.54  fof(f1110,plain,(
% 1.41/0.54    ~r1_tarski(k1_relat_1(sK7),sK5) | spl8_123),
% 1.41/0.54    inference(avatar_component_clause,[],[f1108])).
% 1.41/0.54  fof(f1671,plain,(
% 1.41/0.54    sK6 != k9_relat_1(sK7,sK5) | k1_relat_1(sK7) != k10_relat_1(sK7,sK6) | k1_xboole_0 != k10_relat_1(sK7,k9_relat_1(sK7,k1_xboole_0)) | k1_xboole_0 != sK5 | sK5 = k1_relat_1(sK7)),
% 1.41/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.41/0.54  fof(f1667,plain,(
% 1.41/0.54    spl8_189 | spl8_190 | ~spl8_159 | ~spl8_163),
% 1.41/0.54    inference(avatar_split_clause,[],[f1658,f1506,f1486,f1664,f1660])).
% 1.41/0.54  fof(f1664,plain,(
% 1.41/0.54    spl8_190 <=> k1_xboole_0 = sK5),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_190])])).
% 1.41/0.54  fof(f1486,plain,(
% 1.41/0.54    spl8_159 <=> v1_funct_2(sK7,sK5,k1_xboole_0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_159])])).
% 1.41/0.54  fof(f1506,plain,(
% 1.41/0.54    spl8_163 <=> sP4(sK7,k1_xboole_0,sK5)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_163])])).
% 1.41/0.54  fof(f1658,plain,(
% 1.41/0.54    k1_xboole_0 = sK5 | k1_xboole_0 = sK7 | (~spl8_159 | ~spl8_163)),
% 1.41/0.54    inference(subsumption_resolution,[],[f1657,f1488])).
% 1.41/0.54  fof(f1488,plain,(
% 1.41/0.54    v1_funct_2(sK7,sK5,k1_xboole_0) | ~spl8_159),
% 1.41/0.54    inference(avatar_component_clause,[],[f1486])).
% 1.41/0.54  fof(f1657,plain,(
% 1.41/0.54    ~v1_funct_2(sK7,sK5,k1_xboole_0) | k1_xboole_0 = sK5 | k1_xboole_0 = sK7 | ~spl8_163),
% 1.41/0.54    inference(resolution,[],[f1508,f98])).
% 1.41/0.54  fof(f98,plain,(
% 1.41/0.54    ( ! [X2,X0] : (~sP4(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 1.41/0.54    inference(equality_resolution,[],[f87])).
% 1.41/0.54  fof(f87,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP4(X0,X1,X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f54])).
% 1.41/0.54  fof(f54,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP4(X0,X1,X2))),
% 1.41/0.54    inference(rectify,[],[f53])).
% 1.41/0.54  fof(f53,plain,(
% 1.41/0.54    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 1.41/0.54    inference(nnf_transformation,[],[f46])).
% 1.41/0.54  fof(f46,plain,(
% 1.41/0.54    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 1.41/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.41/0.54  fof(f1508,plain,(
% 1.41/0.54    sP4(sK7,k1_xboole_0,sK5) | ~spl8_163),
% 1.41/0.54    inference(avatar_component_clause,[],[f1506])).
% 1.41/0.54  fof(f1644,plain,(
% 1.41/0.54    sK6 != k2_relat_1(sK7) | k2_relat_1(sK7) != k1_relat_1(k2_funct_1(sK7)) | sK5 != k1_relat_1(sK7) | k1_relat_1(sK7) != k2_relat_1(k2_funct_1(sK7)) | v1_funct_2(k2_funct_1(sK7),sK6,sK5) | ~v1_funct_2(k2_funct_1(sK7),k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7)))),
% 1.41/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.41/0.54  fof(f1631,plain,(
% 1.41/0.54    sK6 != k2_relat_1(sK7) | k2_relat_1(sK7) != k1_relat_1(k2_funct_1(sK7)) | sK5 != k1_relat_1(sK7) | k1_relat_1(sK7) != k2_relat_1(k2_funct_1(sK7)) | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7)))))),
% 1.41/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.41/0.54  fof(f1610,plain,(
% 1.41/0.54    spl8_183 | ~spl8_126 | ~spl8_132),
% 1.41/0.54    inference(avatar_split_clause,[],[f1460,f1189,f1130,f1607])).
% 1.41/0.54  fof(f1130,plain,(
% 1.41/0.54    spl8_126 <=> k1_xboole_0 = sK6),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_126])])).
% 1.41/0.54  fof(f1189,plain,(
% 1.41/0.54    spl8_132 <=> k1_relat_1(sK7) = k10_relat_1(sK7,sK6)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_132])])).
% 1.41/0.54  fof(f1460,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k10_relat_1(sK7,k1_xboole_0) | (~spl8_126 | ~spl8_132)),
% 1.41/0.54    inference(backward_demodulation,[],[f1191,f1132])).
% 1.41/0.54  fof(f1132,plain,(
% 1.41/0.54    k1_xboole_0 = sK6 | ~spl8_126),
% 1.41/0.54    inference(avatar_component_clause,[],[f1130])).
% 1.41/0.54  fof(f1191,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k10_relat_1(sK7,sK6) | ~spl8_132),
% 1.41/0.54    inference(avatar_component_clause,[],[f1189])).
% 1.41/0.54  fof(f1519,plain,(
% 1.41/0.54    spl8_165 | ~spl8_100 | ~spl8_126),
% 1.41/0.54    inference(avatar_split_clause,[],[f1430,f1130,f877,f1516])).
% 1.41/0.54  fof(f1430,plain,(
% 1.41/0.54    k1_xboole_0 = k2_relat_1(sK7) | (~spl8_100 | ~spl8_126)),
% 1.41/0.54    inference(backward_demodulation,[],[f879,f1132])).
% 1.41/0.54  fof(f1509,plain,(
% 1.41/0.54    spl8_163 | ~spl8_51 | ~spl8_126),
% 1.41/0.54    inference(avatar_split_clause,[],[f1428,f1130,f466,f1506])).
% 1.41/0.54  fof(f466,plain,(
% 1.41/0.54    spl8_51 <=> sP4(sK7,sK6,sK5)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 1.41/0.54  fof(f1428,plain,(
% 1.41/0.54    sP4(sK7,k1_xboole_0,sK5) | (~spl8_51 | ~spl8_126)),
% 1.41/0.54    inference(backward_demodulation,[],[f468,f1132])).
% 1.41/0.54  fof(f468,plain,(
% 1.41/0.54    sP4(sK7,sK6,sK5) | ~spl8_51),
% 1.41/0.54    inference(avatar_component_clause,[],[f466])).
% 1.41/0.54  fof(f1489,plain,(
% 1.41/0.54    spl8_159 | ~spl8_7 | ~spl8_126),
% 1.41/0.54    inference(avatar_split_clause,[],[f1424,f1130,f129,f1486])).
% 1.41/0.54  fof(f129,plain,(
% 1.41/0.54    spl8_7 <=> v1_funct_2(sK7,sK5,sK6)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.41/0.54  fof(f1424,plain,(
% 1.41/0.54    v1_funct_2(sK7,sK5,k1_xboole_0) | (~spl8_7 | ~spl8_126)),
% 1.41/0.54    inference(backward_demodulation,[],[f131,f1132])).
% 1.41/0.54  fof(f131,plain,(
% 1.41/0.54    v1_funct_2(sK7,sK5,sK6) | ~spl8_7),
% 1.41/0.54    inference(avatar_component_clause,[],[f129])).
% 1.41/0.54  fof(f1411,plain,(
% 1.41/0.54    ~spl8_7 | ~spl8_44 | ~spl8_97 | spl8_126 | spl8_149),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f1410])).
% 1.41/0.54  fof(f1410,plain,(
% 1.41/0.54    $false | (~spl8_7 | ~spl8_44 | ~spl8_97 | spl8_126 | spl8_149)),
% 1.41/0.54    inference(subsumption_resolution,[],[f1409,f415])).
% 1.41/0.54  fof(f415,plain,(
% 1.41/0.54    sP3(sK5,sK7,sK6) | ~spl8_44),
% 1.41/0.54    inference(avatar_component_clause,[],[f413])).
% 1.41/0.54  fof(f413,plain,(
% 1.41/0.54    spl8_44 <=> sP3(sK5,sK7,sK6)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 1.41/0.54  fof(f1409,plain,(
% 1.41/0.54    ~sP3(sK5,sK7,sK6) | (~spl8_7 | ~spl8_97 | spl8_126 | spl8_149)),
% 1.41/0.54    inference(subsumption_resolution,[],[f1408,f1143])).
% 1.41/0.54  fof(f1143,plain,(
% 1.41/0.54    ( ! [X0] : (~sP2(X0,sK6)) ) | spl8_126),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f1131,f91])).
% 1.41/0.54  fof(f91,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~sP2(X0,X1) | k1_xboole_0 = X1) )),
% 1.41/0.54    inference(cnf_transformation,[],[f57])).
% 1.41/0.54  fof(f57,plain,(
% 1.41/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 1.41/0.54    inference(nnf_transformation,[],[f44])).
% 1.41/0.54  fof(f44,plain,(
% 1.41/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 1.41/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.41/0.54  fof(f1131,plain,(
% 1.41/0.54    k1_xboole_0 != sK6 | spl8_126),
% 1.41/0.54    inference(avatar_component_clause,[],[f1130])).
% 1.41/0.54  fof(f1408,plain,(
% 1.41/0.54    sP2(sK5,sK6) | ~sP3(sK5,sK7,sK6) | (~spl8_7 | ~spl8_97 | spl8_149)),
% 1.41/0.54    inference(subsumption_resolution,[],[f1407,f131])).
% 1.41/0.54  fof(f1407,plain,(
% 1.41/0.54    ~v1_funct_2(sK7,sK5,sK6) | sP2(sK5,sK6) | ~sP3(sK5,sK7,sK6) | (~spl8_97 | spl8_149)),
% 1.41/0.54    inference(subsumption_resolution,[],[f1395,f1353])).
% 1.41/0.54  fof(f1353,plain,(
% 1.41/0.54    sK5 != k1_relat_1(sK7) | spl8_149),
% 1.41/0.54    inference(avatar_component_clause,[],[f1352])).
% 1.41/0.54  fof(f1352,plain,(
% 1.41/0.54    spl8_149 <=> sK5 = k1_relat_1(sK7)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).
% 1.41/0.54  fof(f1395,plain,(
% 1.41/0.54    sK5 = k1_relat_1(sK7) | ~v1_funct_2(sK7,sK5,sK6) | sP2(sK5,sK6) | ~sP3(sK5,sK7,sK6) | ~spl8_97),
% 1.41/0.54    inference(superposition,[],[f849,f89])).
% 1.41/0.54  fof(f89,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP2(X0,X2) | ~sP3(X0,X1,X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f56])).
% 1.41/0.54  fof(f56,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP2(X0,X2) | ~sP3(X0,X1,X2))),
% 1.41/0.54    inference(rectify,[],[f55])).
% 1.41/0.54  fof(f55,plain,(
% 1.41/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 1.41/0.54    inference(nnf_transformation,[],[f45])).
% 1.41/0.54  fof(f45,plain,(
% 1.41/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 1.41/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.41/0.54  fof(f849,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7) | ~spl8_97),
% 1.41/0.54    inference(avatar_component_clause,[],[f847])).
% 1.41/0.54  fof(f847,plain,(
% 1.41/0.54    spl8_97 <=> k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).
% 1.41/0.54  fof(f1340,plain,(
% 1.41/0.54    spl8_147 | ~spl8_5 | ~spl8_8 | ~spl8_10),
% 1.41/0.54    inference(avatar_split_clause,[],[f1329,f150,f134,f119,f1337])).
% 1.41/0.54  fof(f119,plain,(
% 1.41/0.54    spl8_5 <=> v2_funct_1(sK7)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.41/0.54  fof(f134,plain,(
% 1.41/0.54    spl8_8 <=> v1_funct_1(sK7)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.41/0.54  fof(f150,plain,(
% 1.41/0.54    spl8_10 <=> v1_relat_1(sK7)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.41/0.54  fof(f1329,plain,(
% 1.41/0.54    k1_xboole_0 = k10_relat_1(sK7,k9_relat_1(sK7,k1_xboole_0)) | (~spl8_5 | ~spl8_8 | ~spl8_10)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f151,f136,f121,f64,f78])).
% 1.41/0.54  fof(f78,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f31])).
% 1.41/0.54  fof(f31,plain,(
% 1.41/0.54    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(flattening,[],[f30])).
% 1.41/0.54  fof(f30,plain,(
% 1.41/0.54    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.41/0.54    inference(ennf_transformation,[],[f5])).
% 1.41/0.54  fof(f5,axiom,(
% 1.41/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 1.41/0.54  fof(f121,plain,(
% 1.41/0.54    v2_funct_1(sK7) | ~spl8_5),
% 1.41/0.54    inference(avatar_component_clause,[],[f119])).
% 1.41/0.54  fof(f136,plain,(
% 1.41/0.54    v1_funct_1(sK7) | ~spl8_8),
% 1.41/0.54    inference(avatar_component_clause,[],[f134])).
% 1.41/0.54  fof(f151,plain,(
% 1.41/0.54    v1_relat_1(sK7) | ~spl8_10),
% 1.41/0.54    inference(avatar_component_clause,[],[f150])).
% 1.41/0.54  fof(f1192,plain,(
% 1.41/0.54    spl8_132 | ~spl8_5 | ~spl8_8 | ~spl8_10 | ~spl8_107 | ~spl8_115),
% 1.41/0.54    inference(avatar_split_clause,[],[f1187,f976,f934,f150,f134,f119,f1189])).
% 1.41/0.54  fof(f934,plain,(
% 1.41/0.54    spl8_107 <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_relat_1(sK7))))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).
% 1.41/0.54  fof(f976,plain,(
% 1.41/0.54    spl8_115 <=> k1_relat_1(sK7) = k2_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).
% 1.41/0.54  fof(f1187,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k10_relat_1(sK7,sK6) | (~spl8_5 | ~spl8_8 | ~spl8_10 | ~spl8_107 | ~spl8_115)),
% 1.41/0.54    inference(forward_demodulation,[],[f1186,f978])).
% 1.41/0.54  fof(f978,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k2_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7)) | ~spl8_115),
% 1.41/0.54    inference(avatar_component_clause,[],[f976])).
% 1.41/0.54  fof(f1186,plain,(
% 1.41/0.54    k2_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7)) = k10_relat_1(sK7,sK6) | (~spl8_5 | ~spl8_8 | ~spl8_10 | ~spl8_107)),
% 1.41/0.54    inference(forward_demodulation,[],[f1165,f1142])).
% 1.41/0.54  fof(f1142,plain,(
% 1.41/0.54    ( ! [X0] : (k10_relat_1(sK7,X0) = k7_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7),X0)) ) | (~spl8_5 | ~spl8_8 | ~spl8_10 | ~spl8_107)),
% 1.41/0.54    inference(forward_demodulation,[],[f1139,f1047])).
% 1.41/0.54  fof(f1047,plain,(
% 1.41/0.54    ( ! [X0] : (k10_relat_1(sK7,X0) = k9_relat_1(k2_funct_1(sK7),X0)) ) | (~spl8_5 | ~spl8_8 | ~spl8_10)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f151,f136,f121,f73])).
% 1.41/0.54  fof(f73,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f27])).
% 1.41/0.54  fof(f27,plain,(
% 1.41/0.54    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.41/0.54    inference(flattening,[],[f26])).
% 1.41/0.54  fof(f26,plain,(
% 1.41/0.54    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.41/0.54    inference(ennf_transformation,[],[f4])).
% 1.41/0.54  fof(f4,axiom,(
% 1.41/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 1.41/0.54  fof(f1139,plain,(
% 1.41/0.54    ( ! [X0] : (k9_relat_1(k2_funct_1(sK7),X0) = k7_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7),X0)) ) | ~spl8_107),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f936,f95])).
% 1.41/0.54  fof(f936,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_relat_1(sK7)))) | ~spl8_107),
% 1.41/0.54    inference(avatar_component_clause,[],[f934])).
% 1.41/0.54  fof(f1165,plain,(
% 1.41/0.54    k2_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7)) = k7_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7),sK6) | ~spl8_107),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f936,f85])).
% 1.41/0.54  fof(f1185,plain,(
% 1.41/0.54    spl8_131 | ~spl8_4 | ~spl8_6),
% 1.41/0.54    inference(avatar_split_clause,[],[f1180,f124,f114,f1182])).
% 1.41/0.54  fof(f1182,plain,(
% 1.41/0.54    spl8_131 <=> sK6 = k9_relat_1(sK7,sK5)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_131])])).
% 1.41/0.54  fof(f114,plain,(
% 1.41/0.54    spl8_4 <=> sK6 = k2_relset_1(sK5,sK6,sK7)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.41/0.54  fof(f124,plain,(
% 1.41/0.54    spl8_6 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.41/0.54  fof(f1180,plain,(
% 1.41/0.54    sK6 = k9_relat_1(sK7,sK5) | (~spl8_4 | ~spl8_6)),
% 1.41/0.54    inference(forward_demodulation,[],[f1179,f116])).
% 1.41/0.54  fof(f116,plain,(
% 1.41/0.54    sK6 = k2_relset_1(sK5,sK6,sK7) | ~spl8_4),
% 1.41/0.54    inference(avatar_component_clause,[],[f114])).
% 1.41/0.54  fof(f1179,plain,(
% 1.41/0.54    k2_relset_1(sK5,sK6,sK7) = k9_relat_1(sK7,sK5) | ~spl8_6),
% 1.41/0.54    inference(forward_demodulation,[],[f1166,f1140])).
% 1.41/0.54  fof(f1140,plain,(
% 1.41/0.54    ( ! [X0] : (k7_relset_1(sK5,sK6,sK7,X0) = k9_relat_1(sK7,X0)) ) | ~spl8_6),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f126,f95])).
% 1.41/0.54  fof(f126,plain,(
% 1.41/0.54    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~spl8_6),
% 1.41/0.54    inference(avatar_component_clause,[],[f124])).
% 1.41/0.54  fof(f1166,plain,(
% 1.41/0.54    k2_relset_1(sK5,sK6,sK7) = k7_relset_1(sK5,sK6,sK7,sK5) | ~spl8_6),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f126,f85])).
% 1.41/0.54  fof(f1113,plain,(
% 1.41/0.54    ~spl8_123 | ~spl8_1 | ~spl8_13 | ~spl8_88 | spl8_122),
% 1.41/0.54    inference(avatar_split_clause,[],[f1105,f1098,f755,f191,f101,f1108])).
% 1.41/0.54  fof(f1098,plain,(
% 1.41/0.54    spl8_122 <=> sP1(sK5,k2_funct_1(sK7))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).
% 1.41/0.54  fof(f1105,plain,(
% 1.41/0.54    ~r1_tarski(k1_relat_1(sK7),sK5) | (~spl8_1 | ~spl8_13 | ~spl8_88 | spl8_122)),
% 1.41/0.54    inference(resolution,[],[f1100,f816])).
% 1.41/0.54  fof(f1100,plain,(
% 1.41/0.54    ~sP1(sK5,k2_funct_1(sK7)) | spl8_122),
% 1.41/0.54    inference(avatar_component_clause,[],[f1098])).
% 1.41/0.54  fof(f1102,plain,(
% 1.41/0.54    ~spl8_122 | spl8_2 | ~spl8_80 | ~spl8_100),
% 1.41/0.54    inference(avatar_split_clause,[],[f1096,f877,f671,f105,f1098])).
% 1.41/0.54  fof(f105,plain,(
% 1.41/0.54    spl8_2 <=> v1_funct_2(k2_funct_1(sK7),sK6,sK5)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.41/0.54  fof(f1096,plain,(
% 1.41/0.54    ~sP1(sK5,k2_funct_1(sK7)) | (spl8_2 | ~spl8_80 | ~spl8_100)),
% 1.41/0.54    inference(resolution,[],[f892,f107])).
% 1.41/0.54  fof(f107,plain,(
% 1.41/0.54    ~v1_funct_2(k2_funct_1(sK7),sK6,sK5) | spl8_2),
% 1.41/0.54    inference(avatar_component_clause,[],[f105])).
% 1.41/0.54  fof(f892,plain,(
% 1.41/0.54    ( ! [X1] : (v1_funct_2(k2_funct_1(sK7),sK6,X1) | ~sP1(X1,k2_funct_1(sK7))) ) | (~spl8_80 | ~spl8_100)),
% 1.41/0.54    inference(backward_demodulation,[],[f733,f879])).
% 1.41/0.54  fof(f733,plain,(
% 1.41/0.54    ( ! [X1] : (v1_funct_2(k2_funct_1(sK7),k2_relat_1(sK7),X1) | ~sP1(X1,k2_funct_1(sK7))) ) | ~spl8_80),
% 1.41/0.54    inference(superposition,[],[f75,f673])).
% 1.41/0.54  fof(f75,plain,(
% 1.41/0.54    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~sP1(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f51])).
% 1.41/0.54  fof(f979,plain,(
% 1.41/0.54    spl8_115 | ~spl8_98 | ~spl8_100),
% 1.41/0.54    inference(avatar_split_clause,[],[f974,f877,f866,f976])).
% 1.41/0.54  fof(f866,plain,(
% 1.41/0.54    spl8_98 <=> k1_relat_1(sK7) = k2_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_98])])).
% 1.41/0.54  fof(f974,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k2_relset_1(sK6,k1_relat_1(sK7),k2_funct_1(sK7)) | (~spl8_98 | ~spl8_100)),
% 1.41/0.54    inference(forward_demodulation,[],[f868,f879])).
% 1.41/0.54  fof(f868,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k2_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7)) | ~spl8_98),
% 1.41/0.54    inference(avatar_component_clause,[],[f866])).
% 1.41/0.54  fof(f937,plain,(
% 1.41/0.54    spl8_107 | ~spl8_89 | ~spl8_100),
% 1.41/0.54    inference(avatar_split_clause,[],[f893,f877,f763,f934])).
% 1.41/0.54  fof(f763,plain,(
% 1.41/0.54    spl8_89 <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7))))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).
% 1.41/0.54  fof(f893,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,k1_relat_1(sK7)))) | (~spl8_89 | ~spl8_100)),
% 1.41/0.54    inference(backward_demodulation,[],[f765,f879])).
% 1.41/0.54  fof(f765,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7)))) | ~spl8_89),
% 1.41/0.54    inference(avatar_component_clause,[],[f763])).
% 1.41/0.54  fof(f884,plain,(
% 1.41/0.54    spl8_100 | ~spl8_4 | ~spl8_6),
% 1.41/0.54    inference(avatar_split_clause,[],[f883,f124,f114,f877])).
% 1.41/0.54  fof(f883,plain,(
% 1.41/0.54    sK6 = k2_relat_1(sK7) | (~spl8_4 | ~spl8_6)),
% 1.41/0.54    inference(subsumption_resolution,[],[f863,f126])).
% 1.41/0.54  fof(f863,plain,(
% 1.41/0.54    sK6 = k2_relat_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~spl8_4),
% 1.41/0.54    inference(superposition,[],[f116,f83])).
% 1.41/0.54  fof(f869,plain,(
% 1.41/0.54    spl8_98 | ~spl8_88 | ~spl8_89),
% 1.41/0.54    inference(avatar_split_clause,[],[f864,f763,f755,f866])).
% 1.41/0.54  fof(f864,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k2_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7)) | (~spl8_88 | ~spl8_89)),
% 1.41/0.54    inference(forward_demodulation,[],[f861,f757])).
% 1.41/0.54  fof(f861,plain,(
% 1.41/0.54    k2_relat_1(k2_funct_1(sK7)) = k2_relset_1(k2_relat_1(sK7),k1_relat_1(sK7),k2_funct_1(sK7)) | ~spl8_89),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f765,f83])).
% 1.41/0.54  fof(f850,plain,(
% 1.41/0.54    spl8_97 | ~spl8_6),
% 1.41/0.54    inference(avatar_split_clause,[],[f831,f124,f847])).
% 1.41/0.54  fof(f831,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7) | ~spl8_6),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f126,f82])).
% 1.41/0.54  fof(f82,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f33])).
% 1.41/0.54  fof(f33,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f9])).
% 1.41/0.54  fof(f9,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.41/0.54  fof(f766,plain,(
% 1.41/0.54    spl8_89 | ~spl8_5 | ~spl8_8 | ~spl8_10 | ~spl8_84),
% 1.41/0.54    inference(avatar_split_clause,[],[f761,f703,f150,f134,f119,f763])).
% 1.41/0.54  fof(f703,plain,(
% 1.41/0.54    spl8_84 <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7)))))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).
% 1.41/0.54  fof(f761,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7)))) | (~spl8_5 | ~spl8_8 | ~spl8_10 | ~spl8_84)),
% 1.41/0.54    inference(subsumption_resolution,[],[f760,f151])).
% 1.41/0.54  fof(f760,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7)))) | ~v1_relat_1(sK7) | (~spl8_5 | ~spl8_8 | ~spl8_84)),
% 1.41/0.54    inference(subsumption_resolution,[],[f759,f136])).
% 1.41/0.54  fof(f759,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7)))) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | (~spl8_5 | ~spl8_84)),
% 1.41/0.54    inference(subsumption_resolution,[],[f746,f121])).
% 1.41/0.54  fof(f746,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k1_relat_1(sK7)))) | ~v2_funct_1(sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl8_84),
% 1.41/0.54    inference(superposition,[],[f705,f72])).
% 1.41/0.54  fof(f72,plain,(
% 1.41/0.54    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f25])).
% 1.41/0.54  fof(f25,plain,(
% 1.41/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(flattening,[],[f24])).
% 1.41/0.54  fof(f24,plain,(
% 1.41/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f6])).
% 1.41/0.54  fof(f6,axiom,(
% 1.41/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.41/0.54  fof(f705,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7))))) | ~spl8_84),
% 1.41/0.54    inference(avatar_component_clause,[],[f703])).
% 1.41/0.54  fof(f758,plain,(
% 1.41/0.54    spl8_88 | ~spl8_5 | ~spl8_8 | ~spl8_10),
% 1.41/0.54    inference(avatar_split_clause,[],[f744,f150,f134,f119,f755])).
% 1.41/0.54  fof(f744,plain,(
% 1.41/0.54    k1_relat_1(sK7) = k2_relat_1(k2_funct_1(sK7)) | (~spl8_5 | ~spl8_8 | ~spl8_10)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f151,f136,f121,f72])).
% 1.41/0.54  fof(f706,plain,(
% 1.41/0.54    spl8_84 | ~spl8_5 | ~spl8_8 | ~spl8_10 | ~spl8_20),
% 1.41/0.54    inference(avatar_split_clause,[],[f701,f248,f150,f134,f119,f703])).
% 1.41/0.54  fof(f248,plain,(
% 1.41/0.54    spl8_20 <=> m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7)))))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.41/0.54  fof(f701,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7))))) | (~spl8_5 | ~spl8_8 | ~spl8_10 | ~spl8_20)),
% 1.41/0.54    inference(subsumption_resolution,[],[f700,f151])).
% 1.41/0.54  fof(f700,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7))))) | ~v1_relat_1(sK7) | (~spl8_5 | ~spl8_8 | ~spl8_20)),
% 1.41/0.54    inference(subsumption_resolution,[],[f699,f136])).
% 1.41/0.54  fof(f699,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7))))) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | (~spl8_5 | ~spl8_20)),
% 1.41/0.54    inference(subsumption_resolution,[],[f663,f121])).
% 1.41/0.54  fof(f663,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK7))))) | ~v2_funct_1(sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl8_20),
% 1.41/0.54    inference(superposition,[],[f250,f71])).
% 1.41/0.54  fof(f71,plain,(
% 1.41/0.54    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f25])).
% 1.41/0.54  fof(f250,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7))))) | ~spl8_20),
% 1.41/0.54    inference(avatar_component_clause,[],[f248])).
% 1.41/0.54  fof(f674,plain,(
% 1.41/0.54    spl8_80 | ~spl8_5 | ~spl8_8 | ~spl8_10),
% 1.41/0.54    inference(avatar_split_clause,[],[f659,f150,f134,f119,f671])).
% 1.41/0.54  fof(f659,plain,(
% 1.41/0.54    k2_relat_1(sK7) = k1_relat_1(k2_funct_1(sK7)) | (~spl8_5 | ~spl8_8 | ~spl8_10)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f151,f136,f121,f71])).
% 1.41/0.54  fof(f470,plain,(
% 1.41/0.54    spl8_51 | ~spl8_6),
% 1.41/0.54    inference(avatar_split_clause,[],[f454,f124,f466])).
% 1.41/0.54  fof(f454,plain,(
% 1.41/0.54    sP4(sK7,sK6,sK5) | ~spl8_6),
% 1.41/0.54    inference(resolution,[],[f94,f126])).
% 1.41/0.54  fof(f94,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X2,X1,X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f47])).
% 1.41/0.54  fof(f47,plain,(
% 1.41/0.54    ! [X0,X1,X2] : ((sP4(X2,X1,X0) & sP3(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(definition_folding,[],[f38,f46,f45,f44])).
% 1.41/0.54  fof(f38,plain,(
% 1.41/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(flattening,[],[f37])).
% 1.41/0.54  fof(f37,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f13])).
% 1.41/0.54  fof(f13,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.41/0.54  fof(f417,plain,(
% 1.41/0.54    spl8_44 | ~spl8_6),
% 1.41/0.54    inference(avatar_split_clause,[],[f401,f124,f413])).
% 1.41/0.54  fof(f401,plain,(
% 1.41/0.54    sP3(sK5,sK7,sK6) | ~spl8_6),
% 1.41/0.54    inference(resolution,[],[f93,f126])).
% 1.41/0.54  fof(f93,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X0,X2,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f47])).
% 1.41/0.54  fof(f251,plain,(
% 1.41/0.54    spl8_20 | ~spl8_9),
% 1.41/0.54    inference(avatar_split_clause,[],[f244,f140,f248])).
% 1.41/0.54  fof(f140,plain,(
% 1.41/0.54    spl8_9 <=> sP0(k2_funct_1(sK7))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.41/0.54  fof(f244,plain,(
% 1.41/0.54    m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7))))) | ~spl8_9),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f141,f67])).
% 1.41/0.54  fof(f67,plain,(
% 1.41/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~sP0(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f50])).
% 1.41/0.54  fof(f50,plain,(
% 1.41/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP0(X0))),
% 1.41/0.54    inference(nnf_transformation,[],[f40])).
% 1.41/0.54  fof(f40,plain,(
% 1.41/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP0(X0))),
% 1.41/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.41/0.54  fof(f141,plain,(
% 1.41/0.54    sP0(k2_funct_1(sK7)) | ~spl8_9),
% 1.41/0.54    inference(avatar_component_clause,[],[f140])).
% 1.41/0.54  fof(f229,plain,(
% 1.41/0.54    spl8_17 | ~spl8_9),
% 1.41/0.54    inference(avatar_split_clause,[],[f222,f140,f226])).
% 1.41/0.54  fof(f226,plain,(
% 1.41/0.54    spl8_17 <=> v1_funct_2(k2_funct_1(sK7),k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7)))),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.41/0.54  fof(f222,plain,(
% 1.41/0.54    v1_funct_2(k2_funct_1(sK7),k1_relat_1(k2_funct_1(sK7)),k2_relat_1(k2_funct_1(sK7))) | ~spl8_9),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f141,f66])).
% 1.41/0.54  fof(f66,plain,(
% 1.41/0.54    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~sP0(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f50])).
% 1.41/0.54  fof(f213,plain,(
% 1.41/0.54    spl8_13 | ~spl8_8 | ~spl8_10),
% 1.41/0.54    inference(avatar_split_clause,[],[f204,f150,f134,f191])).
% 1.41/0.54  fof(f204,plain,(
% 1.41/0.54    v1_relat_1(k2_funct_1(sK7)) | (~spl8_8 | ~spl8_10)),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f136,f151,f69])).
% 1.41/0.54  fof(f69,plain,(
% 1.41/0.54    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f23])).
% 1.41/0.54  fof(f23,plain,(
% 1.41/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(flattening,[],[f22])).
% 1.41/0.54  fof(f22,plain,(
% 1.41/0.54    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f3])).
% 1.41/0.54  fof(f3,axiom,(
% 1.41/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.41/0.54  fof(f196,plain,(
% 1.41/0.54    spl8_10 | ~spl8_6),
% 1.41/0.54    inference(avatar_split_clause,[],[f179,f124,f150])).
% 1.41/0.54  fof(f179,plain,(
% 1.41/0.54    v1_relat_1(sK7) | ~spl8_6),
% 1.41/0.54    inference(unit_resulting_resolution,[],[f126,f81])).
% 1.41/0.54  fof(f81,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f32])).
% 1.41/0.54  fof(f32,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.54    inference(ennf_transformation,[],[f7])).
% 1.41/0.54  fof(f7,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.54  fof(f194,plain,(
% 1.41/0.54    ~spl8_13 | ~spl8_1 | spl8_9),
% 1.41/0.54    inference(avatar_split_clause,[],[f146,f140,f101,f191])).
% 1.41/0.54  fof(f146,plain,(
% 1.41/0.54    ~v1_funct_1(k2_funct_1(sK7)) | ~v1_relat_1(k2_funct_1(sK7)) | spl8_9),
% 1.41/0.54    inference(resolution,[],[f68,f142])).
% 1.41/0.54  fof(f142,plain,(
% 1.41/0.54    ~sP0(k2_funct_1(sK7)) | spl8_9),
% 1.41/0.54    inference(avatar_component_clause,[],[f140])).
% 1.41/0.54  fof(f68,plain,(
% 1.41/0.54    ( ! [X0] : (sP0(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f41])).
% 1.41/0.54  fof(f41,plain,(
% 1.41/0.54    ! [X0] : (sP0(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(definition_folding,[],[f21,f40])).
% 1.41/0.54  fof(f21,plain,(
% 1.41/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.41/0.54    inference(flattening,[],[f20])).
% 1.41/0.54  fof(f20,plain,(
% 1.41/0.54    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.41/0.54    inference(ennf_transformation,[],[f14])).
% 1.41/0.54  fof(f14,axiom,(
% 1.41/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.41/0.54  fof(f155,plain,(
% 1.41/0.54    ~spl8_10 | spl8_1 | ~spl8_8),
% 1.41/0.54    inference(avatar_split_clause,[],[f154,f134,f101,f150])).
% 1.41/0.54  fof(f154,plain,(
% 1.41/0.54    ~v1_relat_1(sK7) | (spl8_1 | ~spl8_8)),
% 1.41/0.54    inference(subsumption_resolution,[],[f148,f136])).
% 1.41/0.54  fof(f148,plain,(
% 1.41/0.54    ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | spl8_1),
% 1.41/0.54    inference(resolution,[],[f70,f103])).
% 1.41/0.54  fof(f103,plain,(
% 1.41/0.54    ~v1_funct_1(k2_funct_1(sK7)) | spl8_1),
% 1.41/0.54    inference(avatar_component_clause,[],[f101])).
% 1.41/0.54  fof(f70,plain,(
% 1.41/0.54    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f23])).
% 1.41/0.54  fof(f137,plain,(
% 1.41/0.54    spl8_8),
% 1.41/0.54    inference(avatar_split_clause,[],[f58,f134])).
% 1.41/0.54  fof(f58,plain,(
% 1.41/0.54    v1_funct_1(sK7)),
% 1.41/0.54    inference(cnf_transformation,[],[f49])).
% 1.41/0.54  fof(f49,plain,(
% 1.41/0.54    (~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_funct_1(sK7),sK6,sK5) | ~v1_funct_1(k2_funct_1(sK7))) & sK6 = k2_relset_1(sK5,sK6,sK7) & v2_funct_1(sK7) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f19,f48])).
% 1.41/0.54  fof(f48,plain,(
% 1.41/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_funct_1(sK7),sK6,sK5) | ~v1_funct_1(k2_funct_1(sK7))) & sK6 = k2_relset_1(sK5,sK6,sK7) & v2_funct_1(sK7) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f19,plain,(
% 1.41/0.54    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.41/0.54    inference(flattening,[],[f18])).
% 1.41/0.54  fof(f18,plain,(
% 1.41/0.54    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.41/0.54    inference(ennf_transformation,[],[f17])).
% 1.41/0.54  fof(f17,negated_conjecture,(
% 1.41/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.41/0.54    inference(negated_conjecture,[],[f16])).
% 1.41/0.54  fof(f16,conjecture,(
% 1.41/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.41/0.54  fof(f132,plain,(
% 1.41/0.54    spl8_7),
% 1.41/0.54    inference(avatar_split_clause,[],[f59,f129])).
% 1.41/0.54  fof(f59,plain,(
% 1.41/0.54    v1_funct_2(sK7,sK5,sK6)),
% 1.41/0.54    inference(cnf_transformation,[],[f49])).
% 1.41/0.54  fof(f127,plain,(
% 1.41/0.54    spl8_6),
% 1.41/0.54    inference(avatar_split_clause,[],[f60,f124])).
% 1.41/0.54  fof(f60,plain,(
% 1.41/0.54    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.41/0.54    inference(cnf_transformation,[],[f49])).
% 1.41/0.54  fof(f122,plain,(
% 1.41/0.54    spl8_5),
% 1.41/0.54    inference(avatar_split_clause,[],[f61,f119])).
% 1.41/0.54  fof(f61,plain,(
% 1.41/0.54    v2_funct_1(sK7)),
% 1.41/0.54    inference(cnf_transformation,[],[f49])).
% 1.41/0.54  fof(f117,plain,(
% 1.41/0.54    spl8_4),
% 1.41/0.54    inference(avatar_split_clause,[],[f62,f114])).
% 1.41/0.54  fof(f62,plain,(
% 1.41/0.54    sK6 = k2_relset_1(sK5,sK6,sK7)),
% 1.41/0.54    inference(cnf_transformation,[],[f49])).
% 1.41/0.54  fof(f112,plain,(
% 1.41/0.54    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 1.41/0.54    inference(avatar_split_clause,[],[f63,f109,f105,f101])).
% 1.41/0.54  fof(f63,plain,(
% 1.41/0.54    ~m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_funct_1(sK7),sK6,sK5) | ~v1_funct_1(k2_funct_1(sK7))),
% 1.41/0.54    inference(cnf_transformation,[],[f49])).
% 1.41/0.54  % SZS output end Proof for theBenchmark
% 1.41/0.54  % (5434)------------------------------
% 1.41/0.54  % (5434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (5434)Termination reason: Refutation
% 1.41/0.54  
% 1.41/0.54  % (5434)Memory used [KB]: 12537
% 1.41/0.54  % (5434)Time elapsed: 0.099 s
% 1.41/0.54  % (5434)------------------------------
% 1.41/0.54  % (5434)------------------------------
% 1.41/0.55  % (5417)Success in time 0.182 s
%------------------------------------------------------------------------------
