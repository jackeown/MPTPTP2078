%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t37_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:44 EDT 2019

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  704 (3171 expanded)
%              Number of leaves         :  196 (1571 expanded)
%              Depth                    :    9
%              Number of atoms          : 2231 (9494 expanded)
%              Number of equality atoms :  169 ( 497 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1046,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f128,f132,f136,f140,f144,f148,f152,f156,f160,f165,f180,f184,f188,f189,f193,f194,f198,f199,f203,f207,f211,f216,f238,f242,f246,f250,f254,f255,f259,f263,f267,f268,f272,f276,f280,f281,f285,f289,f293,f297,f305,f306,f319,f320,f324,f328,f332,f333,f337,f343,f344,f350,f351,f361,f370,f374,f375,f380,f385,f390,f395,f400,f405,f411,f415,f420,f448,f449,f453,f457,f461,f465,f469,f470,f474,f478,f482,f486,f490,f491,f495,f499,f503,f507,f511,f512,f516,f520,f521,f526,f559,f563,f567,f571,f575,f579,f583,f587,f588,f592,f596,f600,f604,f608,f612,f616,f617,f621,f625,f629,f633,f637,f641,f645,f646,f650,f654,f658,f659,f666,f670,f671,f676,f716,f717,f721,f725,f729,f733,f737,f741,f745,f746,f750,f754,f758,f762,f766,f770,f774,f778,f782,f783,f787,f791,f795,f799,f803,f807,f811,f815,f819,f820,f824,f828,f832,f836,f837,f842,f889,f893,f897,f901,f905,f909,f913,f917,f921,f925,f926,f930,f934,f938,f942,f946,f950,f954,f958,f962,f966,f970,f971,f975,f979,f983,f987,f991,f995,f999,f1003,f1007,f1011,f1015,f1016,f1020,f1024,f1028,f1032,f1036,f1040,f1044,f1045])).

fof(f1045,plain,
    ( spl7_78
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f843,f840,f335])).

fof(f335,plain,
    ( spl7_78
  <=> v1_relat_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f840,plain,
    ( spl7_262
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_262])])).

fof(f843,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK3))
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f841,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',cc1_relset_1)).

fof(f841,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_262 ),
    inference(avatar_component_clause,[],[f840])).

fof(f1044,plain,
    ( spl7_340
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f844,f840,f1042])).

fof(f1042,plain,
    ( spl7_340
  <=> k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_340])])).

fof(f844,plain,
    ( k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK3)) = k1_relat_1(k5_relat_1(sK2,sK3))
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f841,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',redefinition_k1_relset_1)).

fof(f1040,plain,
    ( spl7_338
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f845,f840,f1038])).

fof(f1038,plain,
    ( spl7_338
  <=> m1_subset_1(k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK3)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_338])])).

fof(f845,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK3)),k1_zfmisc_1(sK0))
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f841,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',dt_k1_relset_1)).

fof(f1036,plain,
    ( spl7_336
    | ~ spl7_104
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f846,f840,f413,f1034])).

fof(f1034,plain,
    ( spl7_336
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_336])])).

fof(f413,plain,
    ( spl7_104
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f846,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k5_relat_1(sK2,sK3))
    | ~ spl7_104
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f113,f414,f841,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | r2_relset_1(X0,X1,X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',symmetry_r2_relset_1)).

fof(f414,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f413])).

fof(f113,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f84,f83])).

fof(f83,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',redefinition_k6_partfun1)).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',dt_k6_partfun1)).

fof(f1032,plain,
    ( spl7_334
    | ~ spl7_104
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f847,f840,f413,f1030])).

fof(f1030,plain,
    ( spl7_334
  <=> k5_relat_1(sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_334])])).

fof(f847,plain,
    ( k5_relat_1(sK2,sK3) = k6_relat_1(sK0)
    | ~ spl7_104
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f113,f414,f841,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',redefinition_r2_relset_1)).

fof(f1028,plain,
    ( spl7_332
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f848,f840,f418,f409,f393,f1026])).

fof(f1026,plain,
    ( spl7_332
  <=> k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_332])])).

fof(f393,plain,
    ( spl7_96
  <=> v1_funct_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f409,plain,
    ( spl7_102
  <=> v1_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f418,plain,
    ( spl7_106
  <=> m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f848,plain,
    ( k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3))
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f394,f419,f410,f841,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',redefinition_k1_partfun1)).

fof(f410,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f409])).

fof(f419,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_106 ),
    inference(avatar_component_clause,[],[f418])).

fof(f394,plain,
    ( v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ spl7_96 ),
    inference(avatar_component_clause,[],[f393])).

fof(f1024,plain,
    ( spl7_330
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f849,f840,f524,f409,f398,f1022])).

fof(f1022,plain,
    ( spl7_330
  <=> k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_330])])).

fof(f398,plain,
    ( spl7_98
  <=> v1_funct_1(k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f524,plain,
    ( spl7_144
  <=> m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f849,plain,
    ( k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2))
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f399,f525,f410,f841,f109])).

fof(f525,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_144 ),
    inference(avatar_component_clause,[],[f524])).

fof(f399,plain,
    ( v1_funct_1(k5_relat_1(sK3,sK2))
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f398])).

fof(f1020,plain,
    ( spl7_328
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f850,f840,f674,f409,f403,f1018])).

fof(f1018,plain,
    ( spl7_328
  <=> k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_328])])).

fof(f403,plain,
    ( spl7_100
  <=> v1_funct_1(k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f674,plain,
    ( spl7_200
  <=> m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_200])])).

fof(f850,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2))
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f404,f675,f410,f841,f109])).

fof(f675,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_200 ),
    inference(avatar_component_clause,[],[f674])).

fof(f404,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK2))
    | ~ spl7_100 ),
    inference(avatar_component_clause,[],[f403])).

fof(f1016,plain,
    ( spl7_316
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f851,f840,f409,f993])).

fof(f993,plain,
    ( spl7_316
  <=> k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_316])])).

fof(f851,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f410,f841,f410,f841,f109])).

fof(f1015,plain,
    ( spl7_326
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f852,f840,f409,f158,f150,f1013])).

fof(f1013,plain,
    ( spl7_326
  <=> k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2) = k5_relat_1(k5_relat_1(sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_326])])).

fof(f150,plain,
    ( spl7_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f158,plain,
    ( spl7_16
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f852,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2) = k5_relat_1(k5_relat_1(sK2,sK3),sK2)
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f159,f151,f410,f841,f109])).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f159,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1011,plain,
    ( spl7_324
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f853,f840,f409,f142,f134,f1009])).

fof(f1009,plain,
    ( spl7_324
  <=> k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3) = k5_relat_1(k5_relat_1(sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_324])])).

fof(f134,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f142,plain,
    ( spl7_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f853,plain,
    ( k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3) = k5_relat_1(k5_relat_1(sK2,sK3),sK3)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f143,f135,f410,f841,f109])).

fof(f135,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f143,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f142])).

fof(f1007,plain,
    ( spl7_322
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f854,f840,f418,f409,f393,f1005])).

fof(f1005,plain,
    ( spl7_322
  <=> k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_322])])).

fof(f854,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3))
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f394,f419,f410,f841,f109])).

fof(f1003,plain,
    ( spl7_320
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f855,f840,f524,f409,f398,f1001])).

fof(f1001,plain,
    ( spl7_320
  <=> k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_320])])).

fof(f855,plain,
    ( k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3))
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f399,f525,f410,f841,f109])).

fof(f999,plain,
    ( spl7_318
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f856,f840,f674,f409,f403,f997])).

fof(f997,plain,
    ( spl7_318
  <=> k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_318])])).

fof(f856,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3))
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f404,f675,f410,f841,f109])).

fof(f995,plain,
    ( spl7_316
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f857,f840,f409,f993])).

fof(f857,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f410,f841,f410,f841,f109])).

fof(f991,plain,
    ( spl7_314
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f858,f840,f409,f158,f150,f989])).

fof(f989,plain,
    ( spl7_314
  <=> k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3)) = k5_relat_1(sK2,k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_314])])).

fof(f858,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3)) = k5_relat_1(sK2,k5_relat_1(sK2,sK3))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f159,f151,f410,f841,f109])).

fof(f987,plain,
    ( spl7_312
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f859,f840,f409,f142,f134,f985])).

fof(f985,plain,
    ( spl7_312
  <=> k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3)) = k5_relat_1(sK3,k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_312])])).

fof(f859,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3)) = k5_relat_1(sK3,k5_relat_1(sK2,sK3))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f143,f135,f410,f841,f109])).

fof(f983,plain,
    ( spl7_310
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f860,f840,f418,f409,f393,f981])).

fof(f981,plain,
    ( spl7_310
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_310])])).

fof(f860,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)))
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f394,f419,f410,f841,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',dt_k1_partfun1)).

fof(f979,plain,
    ( spl7_308
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f861,f840,f524,f409,f398,f977])).

fof(f977,plain,
    ( spl7_308
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_308])])).

fof(f861,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)))
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f399,f525,f410,f841,f110])).

fof(f975,plain,
    ( spl7_306
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f862,f840,f674,f409,f403,f973])).

fof(f973,plain,
    ( spl7_306
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_306])])).

fof(f862,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)))
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f404,f675,f410,f841,f110])).

fof(f971,plain,
    ( spl7_294
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f863,f840,f409,f948])).

fof(f948,plain,
    ( spl7_294
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_294])])).

fof(f863,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)))
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f410,f841,f410,f841,f110])).

fof(f970,plain,
    ( spl7_304
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f864,f840,f409,f158,f150,f968])).

fof(f968,plain,
    ( spl7_304
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_304])])).

fof(f864,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f159,f151,f410,f841,f110])).

fof(f966,plain,
    ( spl7_302
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f865,f840,f409,f142,f134,f964])).

fof(f964,plain,
    ( spl7_302
  <=> v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_302])])).

fof(f865,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f143,f135,f410,f841,f110])).

fof(f962,plain,
    ( spl7_300
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f866,f840,f418,f409,f393,f960])).

fof(f960,plain,
    ( spl7_300
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_300])])).

fof(f866,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)))
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f394,f419,f410,f841,f110])).

fof(f958,plain,
    ( spl7_298
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f867,f840,f524,f409,f398,f956])).

fof(f956,plain,
    ( spl7_298
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_298])])).

fof(f867,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)))
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f399,f525,f410,f841,f110])).

fof(f954,plain,
    ( spl7_296
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f868,f840,f674,f409,f403,f952])).

fof(f952,plain,
    ( spl7_296
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_296])])).

fof(f868,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)))
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f404,f675,f410,f841,f110])).

fof(f950,plain,
    ( spl7_294
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f869,f840,f409,f948])).

fof(f869,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)))
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f410,f841,f410,f841,f110])).

fof(f946,plain,
    ( spl7_292
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f870,f840,f409,f158,f150,f944])).

fof(f944,plain,
    ( spl7_292
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_292])])).

fof(f870,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f159,f151,f410,f841,f110])).

fof(f942,plain,
    ( spl7_290
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f871,f840,f409,f142,f134,f940])).

fof(f940,plain,
    ( spl7_290
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_290])])).

fof(f871,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f143,f135,f410,f841,f110])).

fof(f938,plain,
    ( spl7_288
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f872,f840,f418,f409,f393,f936])).

fof(f936,plain,
    ( spl7_288
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_288])])).

fof(f872,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f394,f419,f410,f841,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f934,plain,
    ( spl7_286
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f873,f840,f524,f409,f398,f932])).

fof(f932,plain,
    ( spl7_286
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_286])])).

fof(f873,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f399,f525,f410,f841,f111])).

fof(f930,plain,
    ( spl7_284
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f874,f840,f674,f409,f403,f928])).

fof(f928,plain,
    ( spl7_284
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_284])])).

fof(f874,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f404,f675,f410,f841,f111])).

fof(f926,plain,
    ( spl7_272
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f875,f840,f409,f903])).

fof(f903,plain,
    ( spl7_272
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_272])])).

fof(f875,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f410,f841,f410,f841,f111])).

fof(f925,plain,
    ( spl7_282
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f876,f840,f409,f158,f150,f923])).

fof(f923,plain,
    ( spl7_282
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_282])])).

fof(f876,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK1,k5_relat_1(sK2,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f159,f151,f410,f841,f111])).

fof(f921,plain,
    ( spl7_280
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f877,f840,f409,f142,f134,f919])).

fof(f919,plain,
    ( spl7_280
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_280])])).

fof(f877,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK1,sK0,k5_relat_1(sK2,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f143,f135,f410,f841,f111])).

fof(f917,plain,
    ( spl7_278
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f878,f840,f418,f409,f393,f915])).

fof(f915,plain,
    ( spl7_278
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_278])])).

fof(f878,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_96
    | ~ spl7_102
    | ~ spl7_106
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f394,f419,f410,f841,f111])).

fof(f913,plain,
    ( spl7_276
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f879,f840,f524,f409,f398,f911])).

fof(f911,plain,
    ( spl7_276
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_276])])).

fof(f879,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_98
    | ~ spl7_102
    | ~ spl7_144
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f399,f525,f410,f841,f111])).

fof(f909,plain,
    ( spl7_274
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f880,f840,f674,f409,f403,f907])).

fof(f907,plain,
    ( spl7_274
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_274])])).

fof(f880,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_100
    | ~ spl7_102
    | ~ spl7_200
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f404,f675,f410,f841,f111])).

fof(f905,plain,
    ( spl7_272
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f881,f840,f409,f903])).

fof(f881,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f410,f841,f410,f841,f111])).

fof(f901,plain,
    ( spl7_270
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f882,f840,f409,f158,f150,f899])).

fof(f899,plain,
    ( spl7_270
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_270])])).

fof(f882,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK0,sK2,k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f159,f151,f410,f841,f111])).

fof(f897,plain,
    ( spl7_268
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f883,f840,f409,f142,f134,f895])).

fof(f895,plain,
    ( spl7_268
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_268])])).

fof(f883,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK0,sK3,k5_relat_1(sK2,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_102
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f143,f135,f410,f841,f111])).

fof(f893,plain,
    ( ~ spl7_267
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f884,f840,f891])).

fof(f891,plain,
    ( spl7_267
  <=> ~ sP6(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_267])])).

fof(f884,plain,
    ( ~ sP6(sK0,sK0)
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f841,f123])).

fof(f123,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(general_splitting,[],[f105,f122_D])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f122_D])).

fof(f122_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP6(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',reflexivity_r2_relset_1)).

fof(f889,plain,
    ( spl7_264
    | ~ spl7_262 ),
    inference(avatar_split_clause,[],[f885,f840,f887])).

fof(f887,plain,
    ( spl7_264
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_264])])).

fof(f885,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k5_relat_1(sK2,sK3))
    | ~ spl7_262 ),
    inference(unit_resulting_resolution,[],[f841,f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f842,plain,
    ( spl7_262
    | ~ spl7_46
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f838,f278,f252,f840])).

fof(f252,plain,
    ( spl7_46
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f278,plain,
    ( spl7_58
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f838,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_46
    | ~ spl7_58 ),
    inference(forward_demodulation,[],[f253,f279])).

fof(f279,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f278])).

fof(f253,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f252])).

fof(f837,plain,
    ( spl7_74
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f677,f674,f326])).

fof(f326,plain,
    ( spl7_74
  <=> v1_relat_1(k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f677,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f675,f94])).

fof(f836,plain,
    ( spl7_260
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f678,f674,f834])).

fof(f834,plain,
    ( spl7_260
  <=> k1_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)) = k1_relat_1(k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_260])])).

fof(f678,plain,
    ( k1_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)) = k1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f675,f95])).

fof(f832,plain,
    ( spl7_258
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f679,f674,f830])).

fof(f830,plain,
    ( spl7_258
  <=> m1_subset_1(k1_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_258])])).

fof(f679,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,k5_relat_1(sK2,sK2)),k1_zfmisc_1(sK0))
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f675,f96])).

fof(f828,plain,
    ( spl7_256
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f680,f674,f418,f403,f393,f826])).

fof(f826,plain,
    ( spl7_256
  <=> k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_256])])).

fof(f680,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3))
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f394,f419,f404,f675,f109])).

fof(f824,plain,
    ( spl7_254
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f681,f674,f524,f403,f398,f822])).

fof(f822,plain,
    ( spl7_254
  <=> k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_254])])).

fof(f681,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2))
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f399,f525,f404,f675,f109])).

fof(f820,plain,
    ( spl7_244
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f682,f674,f403,f801])).

fof(f801,plain,
    ( spl7_244
  <=> k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_244])])).

fof(f682,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f404,f675,f404,f675,f109])).

fof(f819,plain,
    ( spl7_252
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f683,f674,f403,f158,f150,f817])).

fof(f817,plain,
    ( spl7_252
  <=> k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2) = k5_relat_1(k5_relat_1(sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_252])])).

fof(f683,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2) = k5_relat_1(k5_relat_1(sK2,sK2),sK2)
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f159,f151,f404,f675,f109])).

fof(f815,plain,
    ( spl7_250
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f684,f674,f403,f142,f134,f813])).

fof(f813,plain,
    ( spl7_250
  <=> k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3) = k5_relat_1(k5_relat_1(sK2,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_250])])).

fof(f684,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3) = k5_relat_1(k5_relat_1(sK2,sK2),sK3)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f143,f135,f404,f675,f109])).

fof(f811,plain,
    ( spl7_248
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f685,f674,f418,f403,f393,f809])).

fof(f809,plain,
    ( spl7_248
  <=> k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_248])])).

fof(f685,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2))
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f394,f419,f404,f675,f109])).

fof(f807,plain,
    ( spl7_246
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f686,f674,f524,f403,f398,f805])).

fof(f805,plain,
    ( spl7_246
  <=> k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_246])])).

fof(f686,plain,
    ( k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2))
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f399,f525,f404,f675,f109])).

fof(f803,plain,
    ( spl7_244
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f687,f674,f403,f801])).

fof(f687,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) = k5_relat_1(k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f404,f675,f404,f675,f109])).

fof(f799,plain,
    ( spl7_242
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f688,f674,f403,f158,f150,f797])).

fof(f797,plain,
    ( spl7_242
  <=> k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)) = k5_relat_1(sK2,k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_242])])).

fof(f688,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)) = k5_relat_1(sK2,k5_relat_1(sK2,sK2))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f159,f151,f404,f675,f109])).

fof(f795,plain,
    ( spl7_240
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f689,f674,f403,f142,f134,f793])).

fof(f793,plain,
    ( spl7_240
  <=> k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_240])])).

fof(f689,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,sK2))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f143,f135,f404,f675,f109])).

fof(f791,plain,
    ( spl7_238
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f690,f674,f418,f403,f393,f789])).

fof(f789,plain,
    ( spl7_238
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_238])])).

fof(f690,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)))
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f394,f419,f404,f675,f110])).

fof(f787,plain,
    ( spl7_236
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f691,f674,f524,f403,f398,f785])).

fof(f785,plain,
    ( spl7_236
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_236])])).

fof(f691,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)))
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f399,f525,f404,f675,f110])).

fof(f783,plain,
    ( spl7_226
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f692,f674,f403,f764])).

fof(f764,plain,
    ( spl7_226
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_226])])).

fof(f692,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)))
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f404,f675,f404,f675,f110])).

fof(f782,plain,
    ( spl7_234
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f693,f674,f403,f158,f150,f780])).

fof(f780,plain,
    ( spl7_234
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_234])])).

fof(f693,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f159,f151,f404,f675,f110])).

fof(f778,plain,
    ( spl7_232
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f694,f674,f403,f142,f134,f776])).

fof(f776,plain,
    ( spl7_232
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_232])])).

fof(f694,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f143,f135,f404,f675,f110])).

fof(f774,plain,
    ( spl7_230
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f695,f674,f418,f403,f393,f772])).

fof(f772,plain,
    ( spl7_230
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_230])])).

fof(f695,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)))
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f394,f419,f404,f675,f110])).

fof(f770,plain,
    ( spl7_228
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f696,f674,f524,f403,f398,f768])).

fof(f768,plain,
    ( spl7_228
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_228])])).

fof(f696,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)))
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f399,f525,f404,f675,f110])).

fof(f766,plain,
    ( spl7_226
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f697,f674,f403,f764])).

fof(f697,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)))
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f404,f675,f404,f675,f110])).

fof(f762,plain,
    ( spl7_224
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f698,f674,f403,f158,f150,f760])).

fof(f760,plain,
    ( spl7_224
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_224])])).

fof(f698,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f159,f151,f404,f675,f110])).

fof(f758,plain,
    ( spl7_222
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f699,f674,f403,f142,f134,f756])).

fof(f756,plain,
    ( spl7_222
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_222])])).

fof(f699,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f143,f135,f404,f675,f110])).

fof(f754,plain,
    ( spl7_220
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f700,f674,f418,f403,f393,f752])).

fof(f752,plain,
    ( spl7_220
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_220])])).

fof(f700,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f394,f419,f404,f675,f111])).

fof(f750,plain,
    ( spl7_218
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f701,f674,f524,f403,f398,f748])).

fof(f748,plain,
    ( spl7_218
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).

fof(f701,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f399,f525,f404,f675,f111])).

fof(f746,plain,
    ( spl7_208
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f702,f674,f403,f727])).

fof(f727,plain,
    ( spl7_208
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_208])])).

fof(f702,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f404,f675,f404,f675,f111])).

fof(f745,plain,
    ( spl7_216
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f703,f674,f403,f158,f150,f743])).

fof(f743,plain,
    ( spl7_216
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_216])])).

fof(f703,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f159,f151,f404,f675,f111])).

fof(f741,plain,
    ( spl7_214
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f704,f674,f403,f142,f134,f739])).

fof(f739,plain,
    ( spl7_214
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_214])])).

fof(f704,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,k5_relat_1(sK2,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f143,f135,f404,f675,f111])).

fof(f737,plain,
    ( spl7_212
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f705,f674,f418,f403,f393,f735])).

fof(f735,plain,
    ( spl7_212
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_212])])).

fof(f705,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_96
    | ~ spl7_100
    | ~ spl7_106
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f394,f419,f404,f675,f111])).

fof(f733,plain,
    ( spl7_210
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f706,f674,f524,f403,f398,f731])).

fof(f731,plain,
    ( spl7_210
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_210])])).

fof(f706,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_98
    | ~ spl7_100
    | ~ spl7_144
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f399,f525,f404,f675,f111])).

fof(f729,plain,
    ( spl7_208
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f707,f674,f403,f727])).

fof(f707,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f404,f675,f404,f675,f111])).

fof(f725,plain,
    ( spl7_206
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f708,f674,f403,f158,f150,f723])).

fof(f723,plain,
    ( spl7_206
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_206])])).

fof(f708,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f159,f151,f404,f675,f111])).

fof(f721,plain,
    ( spl7_204
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f709,f674,f403,f142,f134,f719])).

fof(f719,plain,
    ( spl7_204
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_204])])).

fof(f709,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k5_relat_1(sK2,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_100
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f143,f135,f404,f675,f111])).

fof(f717,plain,
    ( spl7_202
    | spl7_41
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f710,f674,f240,f714])).

fof(f714,plain,
    ( spl7_202
  <=> r2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_202])])).

fof(f240,plain,
    ( spl7_41
  <=> ~ sP6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f710,plain,
    ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl7_41
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f241,f675,f122])).

fof(f241,plain,
    ( ~ sP6(sK1,sK0)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f240])).

fof(f716,plain,
    ( spl7_202
    | ~ spl7_200 ),
    inference(avatar_split_clause,[],[f712,f674,f714])).

fof(f712,plain,
    ( r2_relset_1(sK0,sK1,k5_relat_1(sK2,sK2),k5_relat_1(sK2,sK2))
    | ~ spl7_200 ),
    inference(unit_resulting_resolution,[],[f675,f124])).

fof(f676,plain,
    ( spl7_200
    | ~ spl7_44
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f672,f274,f248,f674])).

fof(f248,plain,
    ( spl7_44
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f274,plain,
    ( spl7_56
  <=> k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f672,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_44
    | ~ spl7_56 ),
    inference(forward_demodulation,[],[f249,f275])).

fof(f275,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f274])).

fof(f249,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f248])).

fof(f671,plain,
    ( spl7_146
    | ~ spl7_144
    | spl7_149 ),
    inference(avatar_split_clause,[],[f660,f561,f524,f557])).

fof(f557,plain,
    ( spl7_146
  <=> r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f561,plain,
    ( spl7_149
  <=> ~ sP6(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_149])])).

fof(f660,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))
    | ~ spl7_144
    | ~ spl7_149 ),
    inference(unit_resulting_resolution,[],[f525,f562,f122])).

fof(f562,plain,
    ( ~ sP6(sK1,sK1)
    | ~ spl7_149 ),
    inference(avatar_component_clause,[],[f561])).

fof(f670,plain,
    ( spl7_198
    | spl7_149 ),
    inference(avatar_split_clause,[],[f661,f561,f668])).

fof(f668,plain,
    ( spl7_198
  <=> r2_relset_1(sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_198])])).

fof(f661,plain,
    ( r2_relset_1(sK1,sK1,k6_relat_1(sK1),k6_relat_1(sK1))
    | ~ spl7_149 ),
    inference(unit_resulting_resolution,[],[f113,f562,f122])).

fof(f666,plain,
    ( spl7_196
    | spl7_149 ),
    inference(avatar_split_clause,[],[f662,f561,f664])).

fof(f664,plain,
    ( spl7_196
  <=> r2_relset_1(sK1,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_196])])).

fof(f662,plain,
    ( r2_relset_1(sK1,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))))
    | ~ spl7_149 ),
    inference(unit_resulting_resolution,[],[f87,f562,f122])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',existence_m1_subset_1)).

fof(f659,plain,
    ( spl7_76
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f527,f524,f330])).

fof(f330,plain,
    ( spl7_76
  <=> v1_relat_1(k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f527,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK2))
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f525,f94])).

fof(f658,plain,
    ( spl7_194
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f528,f524,f656])).

fof(f656,plain,
    ( spl7_194
  <=> k1_relset_1(sK1,sK1,k5_relat_1(sK3,sK2)) = k1_relat_1(k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_194])])).

fof(f528,plain,
    ( k1_relset_1(sK1,sK1,k5_relat_1(sK3,sK2)) = k1_relat_1(k5_relat_1(sK3,sK2))
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f525,f95])).

fof(f654,plain,
    ( spl7_192
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f529,f524,f652])).

fof(f652,plain,
    ( spl7_192
  <=> m1_subset_1(k1_relset_1(sK1,sK1,k5_relat_1(sK3,sK2)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_192])])).

fof(f529,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK1,k5_relat_1(sK3,sK2)),k1_zfmisc_1(sK1))
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f525,f96])).

fof(f650,plain,
    ( spl7_190
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f530,f524,f418,f398,f393,f648])).

fof(f648,plain,
    ( spl7_190
  <=> k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_190])])).

fof(f530,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3))
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f394,f419,f399,f525,f109])).

fof(f646,plain,
    ( spl7_182
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f531,f524,f398,f631])).

fof(f631,plain,
    ( spl7_182
  <=> k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_182])])).

fof(f531,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f399,f525,f399,f525,f109])).

fof(f645,plain,
    ( spl7_188
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f532,f524,f398,f158,f150,f643])).

fof(f643,plain,
    ( spl7_188
  <=> k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2) = k5_relat_1(k5_relat_1(sK3,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_188])])).

fof(f532,plain,
    ( k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2) = k5_relat_1(k5_relat_1(sK3,sK2),sK2)
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f159,f151,f399,f525,f109])).

fof(f641,plain,
    ( spl7_186
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f533,f524,f398,f142,f134,f639])).

fof(f639,plain,
    ( spl7_186
  <=> k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(k5_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_186])])).

fof(f533,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(k5_relat_1(sK3,sK2),sK3)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f143,f135,f399,f525,f109])).

fof(f637,plain,
    ( spl7_184
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f534,f524,f418,f398,f393,f635])).

fof(f635,plain,
    ( spl7_184
  <=> k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_184])])).

fof(f534,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2))
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f394,f419,f399,f525,f109])).

fof(f633,plain,
    ( spl7_182
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f535,f524,f398,f631])).

fof(f535,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)) = k5_relat_1(k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f399,f525,f399,f525,f109])).

fof(f629,plain,
    ( spl7_180
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f536,f524,f398,f158,f150,f627])).

fof(f627,plain,
    ( spl7_180
  <=> k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2)) = k5_relat_1(sK2,k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_180])])).

fof(f536,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2)) = k5_relat_1(sK2,k5_relat_1(sK3,sK2))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f159,f151,f399,f525,f109])).

fof(f625,plain,
    ( spl7_178
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f537,f524,f398,f142,f134,f623])).

fof(f623,plain,
    ( spl7_178
  <=> k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,k5_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_178])])).

fof(f537,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,k5_relat_1(sK3,sK2))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f143,f135,f399,f525,f109])).

fof(f621,plain,
    ( spl7_176
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f538,f524,f418,f398,f393,f619])).

fof(f619,plain,
    ( spl7_176
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_176])])).

fof(f538,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)))
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f394,f419,f399,f525,f110])).

fof(f617,plain,
    ( spl7_168
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f539,f524,f398,f602])).

fof(f602,plain,
    ( spl7_168
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).

fof(f539,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)))
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f399,f525,f399,f525,f110])).

fof(f616,plain,
    ( spl7_174
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f540,f524,f398,f158,f150,f614])).

fof(f614,plain,
    ( spl7_174
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_174])])).

fof(f540,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f159,f151,f399,f525,f110])).

fof(f612,plain,
    ( spl7_172
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f541,f524,f398,f142,f134,f610])).

fof(f610,plain,
    ( spl7_172
  <=> v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).

fof(f541,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f143,f135,f399,f525,f110])).

fof(f608,plain,
    ( spl7_170
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f542,f524,f418,f398,f393,f606])).

fof(f606,plain,
    ( spl7_170
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_170])])).

fof(f542,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)))
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f394,f419,f399,f525,f110])).

fof(f604,plain,
    ( spl7_168
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f543,f524,f398,f602])).

fof(f543,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)))
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f399,f525,f399,f525,f110])).

fof(f600,plain,
    ( spl7_166
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f544,f524,f398,f158,f150,f598])).

fof(f598,plain,
    ( spl7_166
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_166])])).

fof(f544,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f159,f151,f399,f525,f110])).

fof(f596,plain,
    ( spl7_164
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f545,f524,f398,f142,f134,f594])).

fof(f594,plain,
    ( spl7_164
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_164])])).

fof(f545,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f143,f135,f399,f525,f110])).

fof(f592,plain,
    ( spl7_162
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f546,f524,f418,f398,f393,f590])).

fof(f590,plain,
    ( spl7_162
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).

fof(f546,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f394,f419,f399,f525,f111])).

fof(f588,plain,
    ( spl7_154
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f547,f524,f398,f573])).

fof(f573,plain,
    ( spl7_154
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f547,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f399,f525,f399,f525,f111])).

fof(f587,plain,
    ( spl7_160
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f548,f524,f398,f158,f150,f585])).

fof(f585,plain,
    ( spl7_160
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).

fof(f548,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK0,sK1,k5_relat_1(sK3,sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f159,f151,f399,f525,f111])).

fof(f583,plain,
    ( spl7_158
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f549,f524,f398,f142,f134,f581])).

fof(f581,plain,
    ( spl7_158
  <=> m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_158])])).

fof(f549,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f143,f135,f399,f525,f111])).

fof(f579,plain,
    ( spl7_156
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f550,f524,f418,f398,f393,f577])).

fof(f577,plain,
    ( spl7_156
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).

fof(f550,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_96
    | ~ spl7_98
    | ~ spl7_106
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f394,f419,f399,f525,f111])).

fof(f575,plain,
    ( spl7_154
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f551,f524,f398,f573])).

fof(f551,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK1,sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f399,f525,f399,f525,f111])).

fof(f571,plain,
    ( spl7_152
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f552,f524,f398,f158,f150,f569])).

fof(f569,plain,
    ( spl7_152
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_152])])).

fof(f552,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK1,sK2,k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f159,f151,f399,f525,f111])).

fof(f567,plain,
    ( spl7_150
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f553,f524,f398,f142,f134,f565])).

fof(f565,plain,
    ( spl7_150
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f553,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK1,sK3,k5_relat_1(sK3,sK2)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_98
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f143,f135,f399,f525,f111])).

fof(f563,plain,
    ( ~ spl7_149
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f554,f524,f561])).

fof(f554,plain,
    ( ~ sP6(sK1,sK1)
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f525,f123])).

fof(f559,plain,
    ( spl7_146
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f555,f524,f557])).

fof(f555,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK2),k5_relat_1(sK3,sK2))
    | ~ spl7_144 ),
    inference(unit_resulting_resolution,[],[f525,f124])).

fof(f526,plain,
    ( spl7_144
    | ~ spl7_42
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f522,f270,f244,f524])).

fof(f244,plain,
    ( spl7_42
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f270,plain,
    ( spl7_54
  <=> k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f522,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_42
    | ~ spl7_54 ),
    inference(forward_demodulation,[],[f245,f271])).

fof(f271,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f270])).

fof(f245,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f244])).

fof(f521,plain,
    ( spl7_68
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f421,f418,f303])).

fof(f303,plain,
    ( spl7_68
  <=> v1_relat_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f421,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f419,f94])).

fof(f520,plain,
    ( spl7_142
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f422,f418,f518])).

fof(f518,plain,
    ( spl7_142
  <=> k1_relset_1(sK1,sK0,k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f422,plain,
    ( k1_relset_1(sK1,sK0,k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f419,f95])).

fof(f516,plain,
    ( spl7_140
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f423,f418,f514])).

fof(f514,plain,
    ( spl7_140
  <=> m1_subset_1(k1_relset_1(sK1,sK0,k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f423,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f419,f96])).

fof(f512,plain,
    ( spl7_134
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f424,f418,f393,f501])).

fof(f501,plain,
    ( spl7_134
  <=> k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f424,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f394,f419,f394,f419,f109])).

fof(f511,plain,
    ( spl7_138
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f425,f418,f393,f158,f150,f509])).

fof(f509,plain,
    ( spl7_138
  <=> k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2) = k5_relat_1(k5_relat_1(sK3,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f425,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2) = k5_relat_1(k5_relat_1(sK3,sK3),sK2)
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f159,f151,f394,f419,f109])).

fof(f507,plain,
    ( spl7_136
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f426,f418,f393,f142,f134,f505])).

fof(f505,plain,
    ( spl7_136
  <=> k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3) = k5_relat_1(k5_relat_1(sK3,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).

fof(f426,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3) = k5_relat_1(k5_relat_1(sK3,sK3),sK3)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f143,f135,f394,f419,f109])).

fof(f503,plain,
    ( spl7_134
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f427,f418,f393,f501])).

fof(f427,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) = k5_relat_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f394,f419,f394,f419,f109])).

fof(f499,plain,
    ( spl7_132
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f428,f418,f393,f158,f150,f497])).

fof(f497,plain,
    ( spl7_132
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f428,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,sK3))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f159,f151,f394,f419,f109])).

fof(f495,plain,
    ( spl7_130
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f429,f418,f393,f142,f134,f493])).

fof(f493,plain,
    ( spl7_130
  <=> k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3)) = k5_relat_1(sK3,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f429,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3)) = k5_relat_1(sK3,k5_relat_1(sK3,sK3))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f143,f135,f394,f419,f109])).

fof(f491,plain,
    ( spl7_124
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f430,f418,f393,f480])).

fof(f480,plain,
    ( spl7_124
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f430,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)))
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f394,f419,f394,f419,f110])).

fof(f490,plain,
    ( spl7_128
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f431,f418,f393,f158,f150,f488])).

fof(f488,plain,
    ( spl7_128
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f431,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f159,f151,f394,f419,f110])).

fof(f486,plain,
    ( spl7_126
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f432,f418,f393,f142,f134,f484])).

fof(f484,plain,
    ( spl7_126
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f432,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f143,f135,f394,f419,f110])).

fof(f482,plain,
    ( spl7_124
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f433,f418,f393,f480])).

fof(f433,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)))
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f394,f419,f394,f419,f110])).

fof(f478,plain,
    ( spl7_122
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f434,f418,f393,f158,f150,f476])).

fof(f476,plain,
    ( spl7_122
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f434,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f159,f151,f394,f419,f110])).

fof(f474,plain,
    ( spl7_120
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f435,f418,f393,f142,f134,f472])).

fof(f472,plain,
    ( spl7_120
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f435,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f143,f135,f394,f419,f110])).

fof(f470,plain,
    ( spl7_114
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f436,f418,f393,f459])).

fof(f459,plain,
    ( spl7_114
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f436,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f394,f419,f394,f419,f111])).

fof(f469,plain,
    ( spl7_118
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f437,f418,f393,f158,f150,f467])).

fof(f467,plain,
    ( spl7_118
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f437,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,k5_relat_1(sK3,sK3),sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f159,f151,f394,f419,f111])).

fof(f465,plain,
    ( spl7_116
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f438,f418,f393,f142,f134,f463])).

fof(f463,plain,
    ( spl7_116
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f438,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f143,f135,f394,f419,f111])).

fof(f461,plain,
    ( spl7_114
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f439,f418,f393,f459])).

fof(f439,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f394,f419,f394,f419,f111])).

fof(f457,plain,
    ( spl7_112
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f440,f418,f393,f158,f150,f455])).

fof(f455,plain,
    ( spl7_112
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f440,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_12
    | ~ spl7_16
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f159,f151,f394,f419,f111])).

fof(f453,plain,
    ( spl7_110
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f441,f418,f393,f142,f134,f451])).

fof(f451,plain,
    ( spl7_110
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f441,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,k5_relat_1(sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_96
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f143,f135,f394,f419,f111])).

fof(f449,plain,
    ( spl7_108
    | spl7_23
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f442,f418,f182,f446])).

fof(f446,plain,
    ( spl7_108
  <=> r2_relset_1(sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f182,plain,
    ( spl7_23
  <=> ~ sP6(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f442,plain,
    ( r2_relset_1(sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl7_23
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f183,f419,f122])).

fof(f183,plain,
    ( ~ sP6(sK0,sK1)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f182])).

fof(f448,plain,
    ( spl7_108
    | ~ spl7_106 ),
    inference(avatar_split_clause,[],[f444,f418,f446])).

fof(f444,plain,
    ( r2_relset_1(sK1,sK0,k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3))
    | ~ spl7_106 ),
    inference(unit_resulting_resolution,[],[f419,f124])).

fof(f420,plain,
    ( spl7_106
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f416,f196,f186,f418])).

fof(f186,plain,
    ( spl7_24
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f196,plain,
    ( spl7_28
  <=> k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3) = k5_relat_1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f416,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f187,f197])).

fof(f197,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f196])).

fof(f187,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f186])).

fof(f415,plain,
    ( spl7_104
    | ~ spl7_2
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f407,f278,f130,f413])).

fof(f130,plain,
    ( spl7_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f407,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl7_2
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f279,f131])).

fof(f131,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f411,plain,
    ( spl7_102
    | ~ spl7_52
    | ~ spl7_58 ),
    inference(avatar_split_clause,[],[f406,f278,f265,f409])).

fof(f265,plain,
    ( spl7_52
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f406,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl7_52
    | ~ spl7_58 ),
    inference(backward_demodulation,[],[f279,f266])).

fof(f266,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f265])).

fof(f405,plain,
    ( spl7_100
    | ~ spl7_50
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f401,f274,f261,f403])).

fof(f261,plain,
    ( spl7_50
  <=> v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f401,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK2))
    | ~ spl7_50
    | ~ spl7_56 ),
    inference(backward_demodulation,[],[f275,f262])).

fof(f262,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f261])).

fof(f400,plain,
    ( spl7_98
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f396,f270,f257,f398])).

fof(f257,plain,
    ( spl7_48
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f396,plain,
    ( v1_funct_1(k5_relat_1(sK3,sK2))
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(backward_demodulation,[],[f271,f258])).

fof(f258,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f257])).

fof(f395,plain,
    ( spl7_96
    | ~ spl7_26
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f391,f196,f191,f393])).

fof(f191,plain,
    ( spl7_26
  <=> v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f391,plain,
    ( v1_funct_1(k5_relat_1(sK3,sK3))
    | ~ spl7_26
    | ~ spl7_28 ),
    inference(backward_demodulation,[],[f197,f192])).

fof(f192,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f191])).

fof(f390,plain,
    ( ~ spl7_95
    | spl7_87 ),
    inference(avatar_split_clause,[],[f386,f368,f388])).

fof(f388,plain,
    ( spl7_95
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f368,plain,
    ( spl7_87
  <=> ~ sP5(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f386,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl7_87 ),
    inference(unit_resulting_resolution,[],[f81,f369,f120])).

fof(f120,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f120_D])).

fof(f120_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f369,plain,
    ( ~ sP5(sK1)
    | ~ spl7_87 ),
    inference(avatar_component_clause,[],[f368])).

fof(f81,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',dt_o_0_0_xboole_0)).

fof(f385,plain,
    ( spl7_92
    | ~ spl7_60
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f381,f291,f283,f383])).

fof(f383,plain,
    ( spl7_92
  <=> k1_relat_1(sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f283,plain,
    ( spl7_60
  <=> k1_relset_1(sK0,sK1,sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f291,plain,
    ( spl7_64
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f381,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl7_60
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f292,f284])).

fof(f284,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f283])).

fof(f292,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f291])).

fof(f380,plain,
    ( spl7_90
    | ~ spl7_60
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f376,f287,f283,f378])).

fof(f378,plain,
    ( spl7_90
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f287,plain,
    ( spl7_62
  <=> m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f376,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl7_60
    | ~ spl7_62 ),
    inference(forward_demodulation,[],[f288,f284])).

fof(f288,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f287])).

fof(f375,plain,
    ( ~ spl7_89
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f364,f214,f372])).

fof(f372,plain,
    ( spl7_89
  <=> ~ r2_hidden(sK1,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f214,plain,
    ( spl7_36
  <=> r2_hidden(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f364,plain,
    ( ~ r2_hidden(sK1,sK4(sK1))
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f215,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',antisymmetry_r2_hidden)).

fof(f215,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f214])).

fof(f374,plain,
    ( ~ spl7_89
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f365,f214,f372])).

fof(f365,plain,
    ( ~ r2_hidden(sK1,sK4(sK1))
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f215,f88])).

fof(f370,plain,
    ( ~ spl7_87
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f366,f214,f368])).

fof(f366,plain,
    ( ~ sP5(sK1)
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f215,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f104,f120_D])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',t5_subset)).

fof(f361,plain,
    ( spl7_84
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f357,f205,f201,f359])).

fof(f359,plain,
    ( spl7_84
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f201,plain,
    ( spl7_30
  <=> m1_subset_1(k1_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f205,plain,
    ( spl7_32
  <=> k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f357,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl7_30
    | ~ spl7_32 ),
    inference(backward_demodulation,[],[f206,f202])).

fof(f202,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK1))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f201])).

fof(f206,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f205])).

fof(f351,plain,
    ( spl7_38
    | ~ spl7_12
    | spl7_41 ),
    inference(avatar_split_clause,[],[f345,f240,f150,f236])).

fof(f236,plain,
    ( spl7_38
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f345,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_12
    | ~ spl7_41 ),
    inference(unit_resulting_resolution,[],[f151,f241,f122])).

fof(f350,plain,
    ( spl7_82
    | spl7_41 ),
    inference(avatar_split_clause,[],[f346,f240,f348])).

fof(f348,plain,
    ( spl7_82
  <=> r2_relset_1(sK0,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f346,plain,
    ( r2_relset_1(sK0,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl7_41 ),
    inference(unit_resulting_resolution,[],[f87,f241,f122])).

fof(f344,plain,
    ( spl7_20
    | ~ spl7_4
    | spl7_23 ),
    inference(avatar_split_clause,[],[f338,f182,f134,f178])).

fof(f178,plain,
    ( spl7_20
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f338,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl7_4
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f135,f183,f122])).

fof(f343,plain,
    ( spl7_80
    | spl7_23 ),
    inference(avatar_split_clause,[],[f339,f182,f341])).

fof(f341,plain,
    ( spl7_80
  <=> r2_relset_1(sK1,sK0,sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f339,plain,
    ( r2_relset_1(sK1,sK0,sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))),sK4(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f87,f183,f122])).

fof(f337,plain,
    ( spl7_78
    | ~ spl7_34
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f308,f295,f209,f335])).

fof(f209,plain,
    ( spl7_34
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f295,plain,
    ( spl7_66
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f308,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK3))
    | ~ spl7_34
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f210,f296,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',dt_k5_relat_1)).

fof(f296,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_66 ),
    inference(avatar_component_clause,[],[f295])).

fof(f210,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f209])).

fof(f333,plain,
    ( spl7_74
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f309,f295,f326])).

fof(f309,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f296,f296,f91])).

fof(f332,plain,
    ( spl7_76
    | ~ spl7_34
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f311,f295,f209,f330])).

fof(f311,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK2))
    | ~ spl7_34
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f210,f296,f91])).

fof(f328,plain,
    ( spl7_74
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f312,f295,f326])).

fof(f312,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK2))
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f296,f296,f91])).

fof(f324,plain,
    ( ~ spl7_73
    | spl7_1
    | ~ spl7_8
    | ~ spl7_16
    | ~ spl7_34
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f313,f295,f209,f158,f142,f126,f322])).

fof(f322,plain,
    ( spl7_73
  <=> k5_relat_1(sK2,sK3) != k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f126,plain,
    ( spl7_1
  <=> ~ v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f313,plain,
    ( k5_relat_1(sK2,sK3) != k6_relat_1(k1_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_8
    | ~ spl7_16
    | ~ spl7_34
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f210,f143,f159,f127,f296,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',t53_funct_1)).

fof(f127,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f320,plain,
    ( ~ spl7_71
    | spl7_1
    | ~ spl7_16
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f314,f295,f158,f126,f317])).

fof(f317,plain,
    ( spl7_71
  <=> k5_relat_1(sK2,sK2) != k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f314,plain,
    ( k5_relat_1(sK2,sK2) != k6_relat_1(k1_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f296,f159,f159,f127,f296,f86])).

fof(f319,plain,
    ( ~ spl7_71
    | spl7_1
    | ~ spl7_16
    | ~ spl7_66 ),
    inference(avatar_split_clause,[],[f315,f295,f158,f126,f317])).

fof(f315,plain,
    ( k5_relat_1(sK2,sK2) != k6_relat_1(k1_relat_1(sK2))
    | ~ spl7_1
    | ~ spl7_16
    | ~ spl7_66 ),
    inference(unit_resulting_resolution,[],[f296,f159,f127,f159,f296,f86])).

fof(f306,plain,
    ( spl7_68
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f299,f209,f303])).

fof(f299,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f210,f210,f91])).

fof(f305,plain,
    ( spl7_68
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f301,f209,f303])).

fof(f301,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f210,f210,f91])).

fof(f297,plain,
    ( spl7_66
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f217,f150,f295])).

fof(f217,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f151,f94])).

fof(f293,plain,
    ( spl7_64
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f218,f150,f291])).

fof(f218,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f151,f95])).

fof(f289,plain,
    ( spl7_62
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f219,f150,f287])).

fof(f219,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f151,f96])).

fof(f285,plain,
    ( spl7_60
    | spl7_11
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f220,f154,f150,f146,f283])).

fof(f146,plain,
    ( spl7_11
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f154,plain,
    ( spl7_14
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f220,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f147,f155,f151,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',d1_funct_2)).

fof(f155,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f147,plain,
    ( k1_xboole_0 != sK1
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f281,plain,
    ( spl7_56
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f221,f158,f150,f274])).

fof(f221,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f159,f159,f151,f151,f109])).

fof(f280,plain,
    ( spl7_58
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f222,f158,f150,f142,f134,f278])).

fof(f222,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f159,f143,f135,f151,f109])).

fof(f276,plain,
    ( spl7_56
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f223,f158,f150,f274])).

fof(f223,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f159,f159,f151,f151,f109])).

fof(f272,plain,
    ( spl7_54
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f224,f158,f150,f142,f134,f270])).

fof(f224,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f143,f159,f135,f151,f109])).

fof(f268,plain,
    ( spl7_50
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f225,f158,f150,f261])).

fof(f225,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2))
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f159,f159,f151,f151,f110])).

fof(f267,plain,
    ( spl7_52
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f226,f158,f150,f142,f134,f265])).

fof(f226,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f159,f143,f135,f151,f110])).

fof(f263,plain,
    ( spl7_50
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f227,f158,f150,f261])).

fof(f227,plain,
    ( v1_funct_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2))
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f159,f159,f151,f151,f110])).

fof(f259,plain,
    ( spl7_48
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f228,f158,f150,f142,f134,f257])).

fof(f228,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f143,f159,f135,f151,f110])).

fof(f255,plain,
    ( spl7_44
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f229,f158,f150,f248])).

fof(f229,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f159,f159,f151,f151,f111])).

fof(f254,plain,
    ( spl7_46
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f230,f158,f150,f142,f134,f252])).

fof(f230,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f159,f143,f135,f151,f111])).

fof(f250,plain,
    ( spl7_44
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f231,f158,f150,f248])).

fof(f231,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f159,f159,f151,f151,f111])).

fof(f246,plain,
    ( spl7_42
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f232,f158,f150,f142,f134,f244])).

fof(f232,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f143,f159,f135,f151,f111])).

fof(f242,plain,
    ( ~ spl7_41
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f233,f150,f240])).

fof(f233,plain,
    ( ~ sP6(sK1,sK0)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f151,f123])).

fof(f238,plain,
    ( spl7_38
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f234,f150,f236])).

fof(f234,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f151,f124])).

fof(f216,plain,
    ( spl7_36
    | spl7_19 ),
    inference(avatar_split_clause,[],[f212,f163,f214])).

fof(f163,plain,
    ( spl7_19
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f212,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f87,f164,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',t2_subset)).

fof(f164,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f163])).

fof(f211,plain,
    ( spl7_34
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f166,f134,f209])).

fof(f166,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f135,f94])).

fof(f207,plain,
    ( spl7_32
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f167,f134,f205])).

fof(f167,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f135,f95])).

fof(f203,plain,
    ( spl7_30
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f168,f134,f201])).

fof(f168,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK1))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f135,f96])).

fof(f199,plain,
    ( spl7_28
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f169,f142,f134,f196])).

fof(f169,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f143,f143,f135,f135,f109])).

fof(f198,plain,
    ( spl7_28
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f170,f142,f134,f196])).

fof(f170,plain,
    ( k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f143,f143,f135,f135,f109])).

fof(f194,plain,
    ( spl7_26
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f171,f142,f134,f191])).

fof(f171,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f143,f143,f135,f135,f110])).

fof(f193,plain,
    ( spl7_26
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f172,f142,f134,f191])).

fof(f172,plain,
    ( v1_funct_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f143,f143,f135,f135,f110])).

fof(f189,plain,
    ( spl7_24
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f173,f142,f134,f186])).

fof(f173,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f143,f143,f135,f135,f111])).

fof(f188,plain,
    ( spl7_24
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f174,f142,f134,f186])).

fof(f174,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK1,sK0,sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f143,f143,f135,f135,f111])).

fof(f184,plain,
    ( ~ spl7_23
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f175,f134,f182])).

fof(f175,plain,
    ( ~ sP6(sK0,sK1)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f135,f123])).

fof(f180,plain,
    ( spl7_20
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f176,f134,f178])).

fof(f176,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f135,f124])).

fof(f165,plain,
    ( ~ spl7_19
    | spl7_11 ),
    inference(avatar_split_clause,[],[f161,f146,f163])).

fof(f161,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f147,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',t6_boole)).

fof(f160,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f72,f158])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ~ v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f66,f65])).

fof(f65,plain,
    ( ? [X0,X1,X2] :
        ( ~ v2_funct_1(X2)
        & ? [X3] :
            ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ v2_funct_1(sK2)
      & ? [X3] :
          ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ~ ( ~ v2_funct_1(X2)
            & ? [X3] :
                ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ v2_funct_1(X2)
          & ? [X3] :
              ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t37_funct_2.p',t37_funct_2)).

fof(f156,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f73,f154])).

fof(f73,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f152,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f74,f150])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f148,plain,(
    ~ spl7_11 ),
    inference(avatar_split_clause,[],[f75,f146])).

fof(f75,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f67])).

fof(f144,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f76,f142])).

fof(f76,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f140,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f77,f138])).

fof(f138,plain,
    ( spl7_6
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f77,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f136,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f78,f134])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f132,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f112,f130])).

fof(f112,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f79,f83])).

fof(f79,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f67])).

fof(f128,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f80,f126])).

fof(f80,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
