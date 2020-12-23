%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t44_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:50 EDT 2019

% Result     : Theorem 8.03s
% Output     : Refutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :  353 ( 794 expanded)
%              Number of leaves         :  100 ( 330 expanded)
%              Depth                    :   16
%              Number of atoms          : 1161 (2889 expanded)
%              Number of equality atoms :  153 ( 303 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48903,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f188,f192,f196,f200,f204,f208,f212,f216,f220,f234,f399,f1016,f1020,f1105,f1201,f1221,f1320,f1505,f1948,f2213,f2320,f2338,f2443,f2447,f2918,f2966,f3000,f4060,f4508,f16637,f16656,f17065,f17075,f17159,f17176,f17949,f28725,f28730,f28751,f28961,f29282,f29442,f29859,f40418,f42153,f47994,f48055,f48071,f48100,f48651,f48856,f48881,f48883,f48884])).

fof(f48884,plain,
    ( o_0_0_xboole_0 != k1_xboole_0
    | o_0_0_xboole_0 != k1_tarski(sK7(sK1))
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_tarski(sK7(sK1))) ),
    introduced(theory_axiom,[])).

fof(f48883,plain,
    ( o_0_0_xboole_0 != k1_tarski(sK7(sK3(sK1)))
    | o_0_0_xboole_0 != k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_tarski(sK7(sK3(sK1)))) ),
    introduced(theory_axiom,[])).

fof(f48881,plain,
    ( o_0_0_xboole_0 != sK4(sK0,sK1,sK7(sK3(sK1)))
    | k3_xboole_0(sK1,sK4(sK0,sK1,sK7(sK3(sK1)))) != k1_tarski(sK7(sK3(sK1)))
    | k3_xboole_0(sK1,o_0_0_xboole_0) = k1_tarski(sK7(sK3(sK1))) ),
    introduced(theory_axiom,[])).

fof(f48856,plain,
    ( spl11_3320
    | ~ spl11_24
    | ~ spl11_6238 ),
    inference(avatar_split_clause,[],[f48855,f48211,f232,f28964])).

fof(f28964,plain,
    ( spl11_3320
  <=> o_0_0_xboole_0 = k1_tarski(sK7(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3320])])).

fof(f232,plain,
    ( spl11_24
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f48211,plain,
    ( spl11_6238
  <=> k3_xboole_0(sK1,o_0_0_xboole_0) = k1_tarski(sK7(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6238])])).

fof(f48855,plain,
    ( o_0_0_xboole_0 = k1_tarski(sK7(sK3(sK1)))
    | ~ spl11_24
    | ~ spl11_6238 ),
    inference(forward_demodulation,[],[f48854,f239])).

fof(f239,plain,
    ( ! [X5] : k3_xboole_0(o_0_0_xboole_0,X5) = o_0_0_xboole_0
    | ~ spl11_24 ),
    inference(superposition,[],[f153,f235])).

fof(f235,plain,
    ( ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl11_24 ),
    inference(superposition,[],[f130,f233])).

fof(f233,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f232])).

fof(f130,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',t2_boole)).

fof(f153,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',commutativity_k3_xboole_0)).

fof(f48854,plain,
    ( k3_xboole_0(o_0_0_xboole_0,sK1) = k1_tarski(sK7(sK3(sK1)))
    | ~ spl11_6238 ),
    inference(forward_demodulation,[],[f48212,f153])).

fof(f48212,plain,
    ( k3_xboole_0(sK1,o_0_0_xboole_0) = k1_tarski(sK7(sK3(sK1)))
    | ~ spl11_6238 ),
    inference(avatar_component_clause,[],[f48211])).

fof(f48651,plain,
    ( spl11_3292
    | ~ spl11_3289
    | ~ spl11_494
    | ~ spl11_3290 ),
    inference(avatar_split_clause,[],[f37554,f28727,f4058,f28745,f28742])).

fof(f28742,plain,
    ( spl11_3292
  <=> m1_subset_1(sK4(sK0,sK1,sK7(sK3(sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3292])])).

fof(f28745,plain,
    ( spl11_3289
  <=> ~ m1_subset_1(sK7(sK3(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3289])])).

fof(f4058,plain,
    ( spl11_494
  <=> ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,sK1)
        | m1_subset_1(sK4(sK0,sK1,X6),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_494])])).

fof(f28727,plain,
    ( spl11_3290
  <=> m1_subset_1(sK7(sK3(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3290])])).

fof(f37554,plain,
    ( ~ m1_subset_1(sK7(sK3(sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK1,sK7(sK3(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_494
    | ~ spl11_3290 ),
    inference(resolution,[],[f4059,f28728])).

fof(f28728,plain,
    ( m1_subset_1(sK7(sK3(sK1)),sK1)
    | ~ spl11_3290 ),
    inference(avatar_component_clause,[],[f28727])).

fof(f4059,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | m1_subset_1(sK4(sK0,sK1,X6),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_494 ),
    inference(avatar_component_clause,[],[f4058])).

fof(f48100,plain,
    ( k3_xboole_0(sK1,sK3(sK1)) != sK3(sK1)
    | k3_xboole_0(sK1,sK3(sK1)) != sK1
    | ~ v1_zfmisc_1(sK3(sK1))
    | v1_zfmisc_1(sK1) ),
    introduced(theory_axiom,[])).

fof(f48071,plain,
    ( o_0_0_xboole_0 != sK3(sK1)
    | o_0_0_xboole_0 != k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK3(sK1)) ),
    introduced(theory_axiom,[])).

fof(f48055,plain,
    ( spl11_6200
    | ~ spl11_6184 ),
    inference(avatar_split_clause,[],[f48020,f47992,f48053])).

fof(f48053,plain,
    ( spl11_6200
  <=> k3_xboole_0(sK1,sK3(sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6200])])).

fof(f47992,plain,
    ( spl11_6184
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6184])])).

fof(f48020,plain,
    ( k3_xboole_0(sK1,sK3(sK1)) = sK1
    | ~ spl11_6184 ),
    inference(resolution,[],[f47993,f261])).

fof(f261,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f154,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',t3_subset)).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',t28_xboole_1)).

fof(f47993,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK3(sK1)))
    | ~ spl11_6184 ),
    inference(avatar_component_clause,[],[f47992])).

fof(f47994,plain,
    ( spl11_6184
    | ~ spl11_3424
    | ~ spl11_4440 ),
    inference(avatar_split_clause,[],[f47990,f40416,f29444,f47992])).

fof(f29444,plain,
    ( spl11_3424
  <=> k1_tarski(sK7(sK3(sK1))) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3424])])).

fof(f40416,plain,
    ( spl11_4440
  <=> ! [X99] :
        ( m1_subset_1(k1_tarski(X99),k1_zfmisc_1(sK3(sK1)))
        | ~ m1_subset_1(X99,sK3(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4440])])).

fof(f47990,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK3(sK1)))
    | ~ spl11_3424
    | ~ spl11_4440 ),
    inference(forward_demodulation,[],[f47982,f29445])).

fof(f29445,plain,
    ( k1_tarski(sK7(sK3(sK1))) = sK1
    | ~ spl11_3424 ),
    inference(avatar_component_clause,[],[f29444])).

fof(f47982,plain,
    ( m1_subset_1(k1_tarski(sK7(sK3(sK1))),k1_zfmisc_1(sK3(sK1)))
    | ~ spl11_4440 ),
    inference(resolution,[],[f40417,f151])).

fof(f151,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',existence_m1_subset_1)).

fof(f40417,plain,
    ( ! [X99] :
        ( ~ m1_subset_1(X99,sK3(sK1))
        | m1_subset_1(k1_tarski(X99),k1_zfmisc_1(sK3(sK1))) )
    | ~ spl11_4440 ),
    inference(avatar_component_clause,[],[f40416])).

fof(f42153,plain,
    ( spl11_6
    | spl11_4919 ),
    inference(avatar_split_clause,[],[f42151,f42135,f457])).

fof(f457,plain,
    ( spl11_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f42135,plain,
    ( spl11_4919
  <=> ~ v1_zfmisc_1(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4919])])).

fof(f42151,plain,
    ( v1_xboole_0(sK1)
    | ~ spl11_4919 ),
    inference(resolution,[],[f42136,f136])).

fof(f136,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(sK3(X0))
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_zfmisc_1(sK3(X0))
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',rc1_tex_2)).

fof(f42136,plain,
    ( ~ v1_zfmisc_1(sK3(sK1))
    | ~ spl11_4919 ),
    inference(avatar_component_clause,[],[f42135])).

fof(f40418,plain,
    ( spl11_238
    | spl11_4440
    | spl11_7
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f40265,f232,f194,f40416,f2216])).

fof(f2216,plain,
    ( spl11_238
  <=> o_0_0_xboole_0 = sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_238])])).

fof(f194,plain,
    ( spl11_7
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f40265,plain,
    ( ! [X99] :
        ( m1_subset_1(k1_tarski(X99),k1_zfmisc_1(sK3(sK1)))
        | ~ m1_subset_1(X99,sK3(sK1))
        | o_0_0_xboole_0 = sK3(sK1) )
    | ~ spl11_7
    | ~ spl11_24 ),
    inference(superposition,[],[f24235,f5166])).

fof(f5166,plain,
    ( ! [X14,X13] :
        ( k3_xboole_0(k1_tarski(X13),X14) = k1_tarski(X13)
        | ~ m1_subset_1(X13,X14)
        | o_0_0_xboole_0 = X14 )
    | ~ spl11_24 ),
    inference(forward_demodulation,[],[f5159,f233])).

fof(f5159,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,X14)
      | k3_xboole_0(k1_tarski(X13),X14) = k1_tarski(X13)
      | k1_xboole_0 = X14 ) ),
    inference(resolution,[],[f542,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',t6_boole)).

fof(f542,plain,(
    ! [X2,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X1,X2)
      | k3_xboole_0(k1_tarski(X1),X2) = k1_tarski(X1) ) ),
    inference(resolution,[],[f499,f261])).

fof(f499,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f497])).

fof(f497,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f163,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',redefinition_k6_domain_1)).

fof(f163,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',dt_k6_domain_1)).

fof(f24235,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK3(sK1)),k1_zfmisc_1(sK3(sK1)))
    | ~ spl11_7 ),
    inference(superposition,[],[f24217,f153])).

fof(f24217,plain,
    ( ! [X40] : m1_subset_1(k3_xboole_0(sK3(sK1),X40),k1_zfmisc_1(sK3(sK1)))
    | ~ spl11_7 ),
    inference(resolution,[],[f4673,f195])).

fof(f195,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f194])).

fof(f4673,plain,(
    ! [X72,X71] :
      ( v1_xboole_0(X71)
      | m1_subset_1(k3_xboole_0(sK3(X71),X72),k1_zfmisc_1(sK3(X71))) ) ),
    inference(resolution,[],[f623,f511])).

fof(f511,plain,(
    ! [X1] :
      ( m1_subset_1(sK3(X1),k1_zfmisc_1(sK3(X1)))
      | v1_xboole_0(X1) ) ),
    inference(global_subsumption,[],[f135,f505])).

fof(f505,plain,(
    ! [X1] :
      ( v1_xboole_0(sK3(X1))
      | m1_subset_1(sK3(X1),k1_zfmisc_1(sK3(X1)))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f502,f136])).

fof(f502,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(global_subsumption,[],[f131,f500])).

fof(f500,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f496])).

fof(f496,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f163,f132])).

fof(f132,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK2(X0)) = X0
            & m1_subset_1(sK2(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f94,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK2(X0)) = X0
        & m1_subset_1(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',d1_tex_2)).

fof(f131,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f623,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | m1_subset_1(k3_xboole_0(X3,X2),k1_zfmisc_1(X4)) ) ),
    inference(superposition,[],[f602,f153])).

fof(f602,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k3_xboole_0(X4,X5),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f597])).

fof(f597,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k3_xboole_0(X4,X5),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f168,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',redefinition_k9_subset_1)).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',dt_k9_subset_1)).

fof(f29859,plain,
    ( u1_struct_0(sK0) != sK4(sK0,sK1,sK7(sK3(sK1)))
    | u1_struct_0(sK0) != sK4(sK0,sK1,sK7(sK1))
    | k3_xboole_0(sK1,sK4(sK0,sK1,sK7(sK3(sK1)))) != k1_tarski(sK7(sK3(sK1)))
    | k3_xboole_0(sK1,u1_struct_0(sK0)) != sK1
    | k1_tarski(sK7(sK3(sK1))) = sK1 ),
    introduced(theory_axiom,[])).

fof(f29442,plain,
    ( ~ spl11_3291
    | spl11_6
    | spl11_3415 ),
    inference(avatar_split_clause,[],[f29438,f29280,f457,f29440])).

fof(f29440,plain,
    ( spl11_3291
  <=> ~ m1_subset_1(sK7(sK3(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3291])])).

fof(f29280,plain,
    ( spl11_3415
  <=> ~ r2_hidden(sK7(sK3(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3415])])).

fof(f29438,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK7(sK3(sK1)),sK1)
    | ~ spl11_3415 ),
    inference(resolution,[],[f29281,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',t2_subset)).

fof(f29281,plain,
    ( ~ r2_hidden(sK7(sK3(sK1)),sK1)
    | ~ spl11_3415 ),
    inference(avatar_component_clause,[],[f29280])).

fof(f29282,plain,
    ( spl11_3410
    | spl11_3412
    | ~ spl11_3415
    | ~ spl11_3289
    | ~ spl11_1
    | ~ spl11_5
    | ~ spl11_228
    | ~ spl11_3292 ),
    inference(avatar_split_clause,[],[f29263,f28742,f1946,f1010,f176,f28745,f29280,f29277,f29274])).

fof(f29274,plain,
    ( spl11_3410
  <=> u1_struct_0(sK0) = sK4(sK0,sK1,sK7(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3410])])).

fof(f29277,plain,
    ( spl11_3412
  <=> o_0_0_xboole_0 = sK4(sK0,sK1,sK7(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3412])])).

fof(f176,plain,
    ( spl11_1
  <=> ~ v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f1010,plain,
    ( spl11_5
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f1946,plain,
    ( spl11_228
  <=> ! [X1,X0] :
        ( u1_struct_0(sK0) = sK4(sK0,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | o_0_0_xboole_0 = sK4(sK0,X0,X1)
        | ~ m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_228])])).

fof(f29263,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK7(sK3(sK1)),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK3(sK1)),sK1)
    | o_0_0_xboole_0 = sK4(sK0,sK1,sK7(sK3(sK1)))
    | u1_struct_0(sK0) = sK4(sK0,sK1,sK7(sK3(sK1)))
    | ~ spl11_228
    | ~ spl11_3292 ),
    inference(resolution,[],[f28743,f1947])).

fof(f1947,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X0)
        | o_0_0_xboole_0 = sK4(sK0,X0,X1)
        | u1_struct_0(sK0) = sK4(sK0,X0,X1) )
    | ~ spl11_228 ),
    inference(avatar_component_clause,[],[f1946])).

fof(f28743,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK7(sK3(sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_3292 ),
    inference(avatar_component_clause,[],[f28742])).

fof(f28961,plain,(
    ~ spl11_3314 ),
    inference(avatar_contradiction_clause,[],[f28946])).

fof(f28946,plain,
    ( $false
    | ~ spl11_3314 ),
    inference(resolution,[],[f28937,f128])).

fof(f128,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',fc2_xboole_0)).

fof(f28937,plain,
    ( v1_xboole_0(k1_tarski(sK7(sK3(sK1))))
    | ~ spl11_3314 ),
    inference(avatar_component_clause,[],[f28936])).

fof(f28936,plain,
    ( spl11_3314
  <=> v1_xboole_0(k1_tarski(sK7(sK3(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3314])])).

fof(f28751,plain,
    ( ~ spl11_3289
    | spl11_3294
    | ~ spl11_522
    | ~ spl11_3290 ),
    inference(avatar_split_clause,[],[f28733,f28727,f4506,f28749,f28745])).

fof(f28749,plain,
    ( spl11_3294
  <=> k3_xboole_0(sK1,sK4(sK0,sK1,sK7(sK3(sK1)))) = k1_tarski(sK7(sK3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3294])])).

fof(f4506,plain,
    ( spl11_522
  <=> ! [X6] :
        ( k3_xboole_0(sK1,sK4(sK0,sK1,X6)) = k1_tarski(X6)
        | ~ m1_subset_1(X6,sK1)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_522])])).

fof(f28733,plain,
    ( k3_xboole_0(sK1,sK4(sK0,sK1,sK7(sK3(sK1)))) = k1_tarski(sK7(sK3(sK1)))
    | ~ m1_subset_1(sK7(sK3(sK1)),u1_struct_0(sK0))
    | ~ spl11_522
    | ~ spl11_3290 ),
    inference(resolution,[],[f28728,f4507])).

fof(f4507,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,sK1)
        | k3_xboole_0(sK1,sK4(sK0,sK1,X6)) = k1_tarski(X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl11_522 ),
    inference(avatar_component_clause,[],[f4506])).

fof(f28730,plain,
    ( spl11_6
    | spl11_3290
    | spl11_7 ),
    inference(avatar_split_clause,[],[f28719,f194,f28727,f457])).

fof(f28719,plain,
    ( m1_subset_1(sK7(sK3(sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ spl11_7 ),
    inference(resolution,[],[f28616,f134])).

fof(f134,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f28616,plain,
    ( ! [X44] :
        ( ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(X44))
        | m1_subset_1(sK7(sK3(sK1)),X44) )
    | ~ spl11_7 ),
    inference(resolution,[],[f6871,f195])).

fof(f6871,plain,(
    ! [X8,X9] :
      ( v1_xboole_0(X8)
      | m1_subset_1(sK7(sK3(X8)),X9)
      | ~ m1_subset_1(sK3(X8),k1_zfmisc_1(X9)) ) ),
    inference(resolution,[],[f2290,f151])).

fof(f2290,plain,(
    ! [X28,X26,X27] :
      ( ~ m1_subset_1(X26,sK3(X28))
      | ~ m1_subset_1(sK3(X28),k1_zfmisc_1(X27))
      | m1_subset_1(X26,X27)
      | v1_xboole_0(X28) ) ),
    inference(resolution,[],[f436,f135])).

fof(f436,plain,(
    ! [X4,X2,X3] :
      ( v1_xboole_0(X2)
      | m1_subset_1(X4,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,X2) ) ),
    inference(resolution,[],[f171,f157])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',t4_subset)).

fof(f28725,plain,
    ( spl11_3288
    | spl11_7
    | ~ spl11_122 ),
    inference(avatar_split_clause,[],[f28716,f1103,f194,f28723])).

fof(f28723,plain,
    ( spl11_3288
  <=> m1_subset_1(sK7(sK3(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3288])])).

fof(f1103,plain,
    ( spl11_122
  <=> m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_122])])).

fof(f28716,plain,
    ( m1_subset_1(sK7(sK3(sK1)),u1_struct_0(sK0))
    | ~ spl11_7
    | ~ spl11_122 ),
    inference(resolution,[],[f28616,f1104])).

fof(f1104,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_122 ),
    inference(avatar_component_clause,[],[f1103])).

fof(f17949,plain,
    ( ~ spl11_2317
    | spl11_2240
    | ~ spl11_24
    | ~ spl11_522
    | ~ spl11_2340 ),
    inference(avatar_split_clause,[],[f17948,f17157,f4506,f232,f16640,f17063])).

fof(f17063,plain,
    ( spl11_2317
  <=> ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2317])])).

fof(f16640,plain,
    ( spl11_2240
  <=> o_0_0_xboole_0 = k1_tarski(sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2240])])).

fof(f17157,plain,
    ( spl11_2340
  <=> o_0_0_xboole_0 = sK4(sK0,sK1,sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2340])])).

fof(f17948,plain,
    ( o_0_0_xboole_0 = k1_tarski(sK7(sK1))
    | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
    | ~ spl11_24
    | ~ spl11_522
    | ~ spl11_2340 ),
    inference(forward_demodulation,[],[f17947,f239])).

fof(f17947,plain,
    ( k3_xboole_0(o_0_0_xboole_0,sK1) = k1_tarski(sK7(sK1))
    | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
    | ~ spl11_522
    | ~ spl11_2340 ),
    inference(forward_demodulation,[],[f17946,f153])).

fof(f17946,plain,
    ( k3_xboole_0(sK1,o_0_0_xboole_0) = k1_tarski(sK7(sK1))
    | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
    | ~ spl11_522
    | ~ spl11_2340 ),
    inference(forward_demodulation,[],[f17941,f17158])).

fof(f17158,plain,
    ( o_0_0_xboole_0 = sK4(sK0,sK1,sK7(sK1))
    | ~ spl11_2340 ),
    inference(avatar_component_clause,[],[f17157])).

fof(f17941,plain,
    ( k3_xboole_0(sK1,sK4(sK0,sK1,sK7(sK1))) = k1_tarski(sK7(sK1))
    | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
    | ~ spl11_522 ),
    inference(resolution,[],[f4507,f151])).

fof(f17176,plain,
    ( ~ spl11_2071
    | spl11_6
    | spl11_2243 ),
    inference(avatar_split_clause,[],[f17175,f16658,f457,f14863])).

fof(f14863,plain,
    ( spl11_2071
  <=> ~ m1_subset_1(sK7(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2071])])).

fof(f16658,plain,
    ( spl11_2243
  <=> ~ r2_hidden(sK7(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2243])])).

fof(f17175,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK7(sK1),sK1)
    | ~ spl11_2243 ),
    inference(resolution,[],[f16659,f157])).

fof(f16659,plain,
    ( ~ r2_hidden(sK7(sK1),sK1)
    | ~ spl11_2243 ),
    inference(avatar_component_clause,[],[f16658])).

fof(f17159,plain,
    ( spl11_2338
    | spl11_2340
    | ~ spl11_2243
    | ~ spl11_2317
    | ~ spl11_1
    | ~ spl11_5
    | ~ spl11_228
    | ~ spl11_2314 ),
    inference(avatar_split_clause,[],[f17143,f17060,f1946,f1010,f176,f17063,f16658,f17157,f17154])).

fof(f17154,plain,
    ( spl11_2338
  <=> u1_struct_0(sK0) = sK4(sK0,sK1,sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2338])])).

fof(f17060,plain,
    ( spl11_2314
  <=> m1_subset_1(sK4(sK0,sK1,sK7(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2314])])).

fof(f17143,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK7(sK1),sK1)
    | o_0_0_xboole_0 = sK4(sK0,sK1,sK7(sK1))
    | u1_struct_0(sK0) = sK4(sK0,sK1,sK7(sK1))
    | ~ spl11_228
    | ~ spl11_2314 ),
    inference(resolution,[],[f17061,f1947])).

fof(f17061,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK7(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_2314 ),
    inference(avatar_component_clause,[],[f17060])).

fof(f17075,plain,
    ( ~ spl11_2071
    | ~ spl11_4
    | spl11_7
    | spl11_2317 ),
    inference(avatar_split_clause,[],[f17073,f17063,f194,f190,f14863])).

fof(f190,plain,
    ( spl11_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f17073,plain,
    ( ~ m1_subset_1(sK7(sK1),sK1)
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_2317 ),
    inference(resolution,[],[f17064,f2293])).

fof(f2293,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(resolution,[],[f2289,f191])).

fof(f191,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f190])).

fof(f2289,plain,
    ( ! [X24,X25] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X25))
        | m1_subset_1(X24,X25)
        | ~ m1_subset_1(X24,sK1) )
    | ~ spl11_7 ),
    inference(resolution,[],[f436,f195])).

fof(f17064,plain,
    ( ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
    | ~ spl11_2317 ),
    inference(avatar_component_clause,[],[f17063])).

fof(f17065,plain,
    ( spl11_2314
    | ~ spl11_2317
    | ~ spl11_494 ),
    inference(avatar_split_clause,[],[f17054,f4058,f17063,f17060])).

fof(f17054,plain,
    ( ~ m1_subset_1(sK7(sK1),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK1,sK7(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_494 ),
    inference(resolution,[],[f4059,f151])).

fof(f16656,plain,(
    spl11_2071 ),
    inference(avatar_contradiction_clause,[],[f16654])).

fof(f16654,plain,
    ( $false
    | ~ spl11_2071 ),
    inference(resolution,[],[f14864,f151])).

fof(f14864,plain,
    ( ~ m1_subset_1(sK7(sK1),sK1)
    | ~ spl11_2071 ),
    inference(avatar_component_clause,[],[f14863])).

fof(f16637,plain,(
    ~ spl11_886 ),
    inference(avatar_contradiction_clause,[],[f16624])).

fof(f16624,plain,
    ( $false
    | ~ spl11_886 ),
    inference(resolution,[],[f6823,f128])).

fof(f6823,plain,
    ( v1_xboole_0(k1_tarski(sK7(sK1)))
    | ~ spl11_886 ),
    inference(avatar_component_clause,[],[f6822])).

fof(f6822,plain,
    ( spl11_886
  <=> v1_xboole_0(k1_tarski(sK7(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_886])])).

fof(f4508,plain,
    ( spl11_6
    | ~ spl11_5
    | spl11_522
    | ~ spl11_0
    | ~ spl11_8
    | ~ spl11_104 ),
    inference(avatar_split_clause,[],[f4504,f1013,f198,f183,f4506,f1010,f457])).

fof(f183,plain,
    ( spl11_0
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f198,plain,
    ( spl11_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f1013,plain,
    ( spl11_104
  <=> ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_104])])).

fof(f4504,plain,
    ( ! [X6] :
        ( k3_xboole_0(sK1,sK4(sK0,sK1,X6)) = k1_tarski(X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X6,sK1) )
    | ~ spl11_0
    | ~ spl11_8
    | ~ spl11_104 ),
    inference(forward_demodulation,[],[f4503,f153])).

fof(f4503,plain,
    ( ! [X6] :
        ( k3_xboole_0(sK4(sK0,sK1,X6),sK1) = k1_tarski(X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X6,sK1) )
    | ~ spl11_0
    | ~ spl11_8
    | ~ spl11_104 ),
    inference(forward_demodulation,[],[f4501,f1014])).

fof(f1014,plain,
    ( ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)
    | ~ spl11_104 ),
    inference(avatar_component_clause,[],[f1013])).

fof(f4501,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X6)) = k1_tarski(X6)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X6,sK1) )
    | ~ spl11_0
    | ~ spl11_8 ),
    inference(resolution,[],[f2130,f184])).

fof(f184,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f183])).

fof(f2130,plain,
    ( ! [X2,X1] :
        ( ~ v2_tex_2(X2,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X2,sK4(sK0,X2,X1)) = k1_tarski(X1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X1,X2) )
    | ~ spl11_8 ),
    inference(resolution,[],[f1866,f157])).

fof(f1866,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),X1,sK4(sK0,X1,X0)) = k1_tarski(X0) )
    | ~ spl11_8 ),
    inference(resolution,[],[f140,f199])).

fof(f199,plain,
    ( l1_pre_topc(sK0)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f198])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = k1_tarski(X2) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = k1_tarski(X2)
                & v3_pre_topc(sK4(X0,X1,X2),X0)
                & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f99])).

fof(f99,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = k1_tarski(X2)
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',t32_tex_2)).

fof(f4060,plain,
    ( spl11_6
    | ~ spl11_5
    | spl11_494
    | ~ spl11_0
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f4055,f198,f183,f4058,f1010,f457])).

fof(f4055,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,sK1,X6),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X6,sK1) )
    | ~ spl11_0
    | ~ spl11_8 ),
    inference(resolution,[],[f2028,f184])).

fof(f2028,plain,
    ( ! [X2,X1] :
        ( ~ v2_tex_2(X2,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,X2,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X1,X2) )
    | ~ spl11_8 ),
    inference(resolution,[],[f1644,f157])).

fof(f1644,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(sK0,X1,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_8 ),
    inference(resolution,[],[f138,f199])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f3000,plain,
    ( spl11_380
    | ~ spl11_378 ),
    inference(avatar_split_clause,[],[f2992,f2964,f2994])).

fof(f2994,plain,
    ( spl11_380
  <=> k3_xboole_0(sK1,sK3(sK1)) = sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_380])])).

fof(f2964,plain,
    ( spl11_378
  <=> k3_xboole_0(sK3(sK1),sK1) = sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_378])])).

fof(f2992,plain,
    ( k3_xboole_0(sK1,sK3(sK1)) = sK3(sK1)
    | ~ spl11_378 ),
    inference(superposition,[],[f153,f2965])).

fof(f2965,plain,
    ( k3_xboole_0(sK3(sK1),sK1) = sK3(sK1)
    | ~ spl11_378 ),
    inference(avatar_component_clause,[],[f2964])).

fof(f2966,plain,
    ( spl11_378
    | ~ spl11_366 ),
    inference(avatar_split_clause,[],[f2961,f2942,f2964])).

fof(f2942,plain,
    ( spl11_366
  <=> m1_subset_1(sK3(sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_366])])).

fof(f2961,plain,
    ( k3_xboole_0(sK3(sK1),sK1) = sK3(sK1)
    | ~ spl11_366 ),
    inference(resolution,[],[f2943,f261])).

fof(f2943,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(sK1))
    | ~ spl11_366 ),
    inference(avatar_component_clause,[],[f2942])).

fof(f2918,plain,
    ( spl11_6
    | spl11_367 ),
    inference(avatar_split_clause,[],[f2916,f2905,f457])).

fof(f2905,plain,
    ( spl11_367
  <=> ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_367])])).

fof(f2916,plain,
    ( v1_xboole_0(sK1)
    | ~ spl11_367 ),
    inference(resolution,[],[f2906,f134])).

fof(f2906,plain,
    ( ~ m1_subset_1(sK3(sK1),k1_zfmisc_1(sK1))
    | ~ spl11_367 ),
    inference(avatar_component_clause,[],[f2905])).

fof(f2447,plain,
    ( ~ spl11_9
    | spl11_255 ),
    inference(avatar_split_clause,[],[f2446,f2336,f1196])).

fof(f1196,plain,
    ( spl11_9
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f2336,plain,
    ( spl11_255
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_255])])).

fof(f2446,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl11_255 ),
    inference(resolution,[],[f2337,f137])).

fof(f137,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',dt_l1_pre_topc)).

fof(f2337,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl11_255 ),
    inference(avatar_component_clause,[],[f2336])).

fof(f2443,plain,
    ( spl11_6
    | ~ spl11_3
    | spl11_251 ),
    inference(avatar_split_clause,[],[f2321,f2318,f179,f457])).

fof(f179,plain,
    ( spl11_3
  <=> ~ v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f2318,plain,
    ( spl11_251
  <=> ~ m1_subset_1(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_251])])).

fof(f2321,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ spl11_251 ),
    inference(resolution,[],[f2319,f131])).

fof(f2319,plain,
    ( ~ m1_subset_1(sK2(sK1),sK1)
    | ~ spl11_251 ),
    inference(avatar_component_clause,[],[f2318])).

fof(f2338,plain,
    ( spl11_14
    | ~ spl11_255
    | ~ spl11_138 ),
    inference(avatar_split_clause,[],[f2329,f1206,f2336,f1193])).

fof(f1193,plain,
    ( spl11_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f1206,plain,
    ( spl11_138
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_138])])).

fof(f2329,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_138 ),
    inference(resolution,[],[f1207,f143])).

fof(f143,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',fc2_struct_0)).

fof(f1207,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_138 ),
    inference(avatar_component_clause,[],[f1206])).

fof(f2320,plain,
    ( ~ spl11_251
    | ~ spl11_4
    | spl11_7
    | spl11_161 ),
    inference(avatar_split_clause,[],[f2311,f1503,f194,f190,f2318])).

fof(f1503,plain,
    ( spl11_161
  <=> ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_161])])).

fof(f2311,plain,
    ( ~ m1_subset_1(sK2(sK1),sK1)
    | ~ spl11_4
    | ~ spl11_7
    | ~ spl11_161 ),
    inference(resolution,[],[f2293,f1504])).

fof(f1504,plain,
    ( ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ spl11_161 ),
    inference(avatar_component_clause,[],[f1503])).

fof(f2213,plain,
    ( spl11_6
    | ~ spl11_128 ),
    inference(avatar_split_clause,[],[f2207,f1117,f457])).

fof(f1117,plain,
    ( spl11_128
  <=> v1_xboole_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_128])])).

fof(f2207,plain,
    ( v1_xboole_0(sK1)
    | ~ spl11_128 ),
    inference(resolution,[],[f1118,f135])).

fof(f1118,plain,
    ( v1_xboole_0(sK3(sK1))
    | ~ spl11_128 ),
    inference(avatar_component_clause,[],[f1117])).

fof(f1948,plain,
    ( ~ spl11_9
    | spl11_228
    | ~ spl11_154 ),
    inference(avatar_split_clause,[],[f1944,f1318,f1946,f1196])).

fof(f1318,plain,
    ( spl11_154
  <=> ! [X0] :
        ( o_0_0_xboole_0 = X0
        | u1_struct_0(sK0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_154])])).

fof(f1944,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(sK0) = sK4(sK0,X0,X1)
        | ~ m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | o_0_0_xboole_0 = sK4(sK0,X0,X1)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl11_154 ),
    inference(resolution,[],[f1319,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f1319,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | u1_struct_0(sK0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | o_0_0_xboole_0 = X0 )
    | ~ spl11_154 ),
    inference(avatar_component_clause,[],[f1318])).

fof(f1505,plain,
    ( ~ spl11_3
    | spl11_6
    | ~ spl11_161
    | spl11_1
    | ~ spl11_146 ),
    inference(avatar_split_clause,[],[f1501,f1219,f176,f1503,f457,f179])).

fof(f1219,plain,
    ( spl11_146
  <=> ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_146])])).

fof(f1501,plain,
    ( ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1)
    | ~ spl11_1
    | ~ spl11_146 ),
    inference(resolution,[],[f1227,f177])).

fof(f177,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f176])).

fof(f1227,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | ~ m1_subset_1(sK2(X0),u1_struct_0(sK0))
        | v1_xboole_0(X0)
        | ~ v1_zfmisc_1(X0) )
    | ~ spl11_146 ),
    inference(superposition,[],[f1220,f490])).

fof(f490,plain,(
    ! [X0] :
      ( k1_tarski(sK2(X0)) = X0
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(global_subsumption,[],[f131,f489])).

fof(f489,plain,(
    ! [X0] :
      ( k1_tarski(sK2(X0)) = X0
      | ~ m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f486])).

fof(f486,plain,(
    ! [X0] :
      ( k1_tarski(sK2(X0)) = X0
      | ~ m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f162,f132])).

fof(f1220,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_146 ),
    inference(avatar_component_clause,[],[f1219])).

fof(f1320,plain,
    ( ~ spl11_9
    | ~ spl11_11
    | spl11_154
    | ~ spl11_12
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f1313,f232,f206,f1318,f1315,f1196])).

fof(f1315,plain,
    ( spl11_11
  <=> ~ v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f206,plain,
    ( spl11_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f1313,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | u1_struct_0(sK0) = X0 )
    | ~ spl11_12
    | ~ spl11_24 ),
    inference(forward_demodulation,[],[f1312,f233])).

fof(f1312,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | u1_struct_0(sK0) = X0 )
    | ~ spl11_12 ),
    inference(resolution,[],[f144,f207])).

fof(f207,plain,
    ( v2_pre_topc(sK0)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f206])).

fof(f144,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(X0)
      | k1_xboole_0 = X2
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X2 ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ( u1_struct_0(X0) != sK5(X0)
            & k1_xboole_0 != sK5(X0)
            & v3_pre_topc(sK5(X0),X0)
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f102,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ? [X1] :
          ( u1_struct_0(X0) != X1
          & k1_xboole_0 != X1
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( u1_struct_0(X0) != sK5(X0)
        & k1_xboole_0 != sK5(X0)
        & v3_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( u1_struct_0(X0) = X1
              | k1_xboole_0 = X1
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( u1_struct_0(X0) != X1
                & k1_xboole_0 != X1
                & v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',t20_tdlat_3)).

fof(f1221,plain,
    ( spl11_138
    | spl11_146
    | ~ spl11_136 ),
    inference(avatar_split_clause,[],[f1204,f1199,f1219,f1206])).

fof(f1199,plain,
    ( spl11_136
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_136])])).

fof(f1204,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl11_136 ),
    inference(duplicate_literal_removal,[],[f1203])).

fof(f1203,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl11_136 ),
    inference(superposition,[],[f1200,f162])).

fof(f1200,plain,
    ( ! [X0] :
        ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_136 ),
    inference(avatar_component_clause,[],[f1199])).

fof(f1201,plain,
    ( spl11_14
    | ~ spl11_9
    | spl11_136
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f1191,f206,f1199,f1196,f1193])).

fof(f1191,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X0),sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_12 ),
    inference(resolution,[],[f142,f207])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',t36_tex_2)).

fof(f1105,plain,
    ( spl11_6
    | spl11_122
    | ~ spl11_104
    | ~ spl11_106 ),
    inference(avatar_split_clause,[],[f1095,f1018,f1013,f1103,f457])).

fof(f1018,plain,
    ( spl11_106
  <=> ! [X1] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_106])])).

fof(f1095,plain,
    ( m1_subset_1(sK3(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ spl11_104
    | ~ spl11_106 ),
    inference(superposition,[],[f1050,f401])).

fof(f401,plain,(
    ! [X3] :
      ( k3_xboole_0(X3,sK3(X3)) = sK3(X3)
      | v1_xboole_0(X3) ) ),
    inference(forward_demodulation,[],[f393,f153])).

fof(f393,plain,(
    ! [X3] :
      ( k3_xboole_0(sK3(X3),X3) = sK3(X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f261,f134])).

fof(f1050,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_104
    | ~ spl11_106 ),
    inference(superposition,[],[f1033,f153])).

fof(f1033,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_104
    | ~ spl11_106 ),
    inference(superposition,[],[f1019,f1014])).

fof(f1019,plain,
    ( ! [X1] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_106 ),
    inference(avatar_component_clause,[],[f1018])).

fof(f1020,plain,
    ( ~ spl11_5
    | spl11_106
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f1006,f190,f1018,f1010])).

fof(f1006,plain,
    ( ! [X1] :
        ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_4 ),
    inference(superposition,[],[f168,f657])).

fof(f657,plain,
    ( ! [X20] : k9_subset_1(u1_struct_0(sK0),X20,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X20)
    | ~ spl11_4 ),
    inference(resolution,[],[f170,f191])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',commutativity_k9_subset_1)).

fof(f1016,plain,
    ( ~ spl11_5
    | spl11_104
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f1005,f190,f1013,f1010])).

fof(f1005,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_4 ),
    inference(superposition,[],[f169,f657])).

fof(f399,plain,
    ( spl11_56
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f391,f190,f397])).

fof(f397,plain,
    ( spl11_56
  <=> k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f391,plain,
    ( k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1
    | ~ spl11_4 ),
    inference(resolution,[],[f261,f191])).

fof(f234,plain,
    ( spl11_24
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f229,f214,f232])).

fof(f214,plain,
    ( spl11_16
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f229,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl11_16 ),
    inference(resolution,[],[f141,f215])).

fof(f215,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f214])).

fof(f220,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f127,f218])).

fof(f218,plain,
    ( spl11_18
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f127,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',fc1_xboole_0)).

fof(f216,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f126,f214])).

fof(f126,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',dt_o_0_0_xboole_0)).

fof(f212,plain,(
    ~ spl11_15 ),
    inference(avatar_split_clause,[],[f118,f210])).

fof(f210,plain,
    ( spl11_15
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f118,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f89,f91,f90])).

fof(f90,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ( ~ v1_zfmisc_1(sK1)
          | ~ v2_tex_2(sK1,X0) )
        & ( v1_zfmisc_1(sK1)
          | v2_tex_2(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t44_tex_2.p',t44_tex_2)).

fof(f208,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f119,f206])).

fof(f119,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f92])).

fof(f204,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f120,f202])).

fof(f202,plain,
    ( spl11_10
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f120,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f92])).

fof(f200,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f121,f198])).

fof(f121,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f92])).

fof(f196,plain,(
    ~ spl11_7 ),
    inference(avatar_split_clause,[],[f122,f194])).

fof(f122,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f92])).

fof(f192,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f123,f190])).

fof(f123,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f92])).

fof(f188,plain,
    ( spl11_0
    | spl11_2 ),
    inference(avatar_split_clause,[],[f124,f186,f183])).

fof(f186,plain,
    ( spl11_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f124,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f92])).

fof(f181,plain,
    ( ~ spl11_1
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f125,f179,f176])).

fof(f125,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f92])).
%------------------------------------------------------------------------------
