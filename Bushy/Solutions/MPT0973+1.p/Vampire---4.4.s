%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t19_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:41 EDT 2019

% Result     : Theorem 9.86s
% Output     : Refutation 9.86s
% Verified   : 
% Statistics : Number of formulae       :  903 (4428 expanded)
%              Number of leaves         :  217 (1621 expanded)
%              Depth                    :   17
%              Number of atoms          : 2497 (12343 expanded)
%              Number of equality atoms :  215 (1574 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24651,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f127,f134,f144,f153,f161,f168,f178,f185,f203,f210,f233,f249,f264,f271,f282,f290,f297,f304,f311,f318,f325,f332,f410,f417,f465,f472,f479,f486,f506,f513,f520,f532,f583,f590,f598,f616,f623,f630,f638,f646,f657,f687,f694,f701,f708,f801,f840,f849,f874,f877,f896,f898,f900,f910,f926,f933,f956,f963,f987,f997,f1022,f1029,f1245,f1301,f1314,f1321,f1328,f1336,f1343,f1350,f1357,f1364,f1372,f1379,f1386,f1393,f1400,f1504,f1511,f1646,f1765,f1987,f2136,f2155,f2162,f2181,f2368,f2640,f2898,f3112,f3119,f3187,f3194,f3201,f3208,f3215,f3290,f3297,f3304,f3311,f5005,f5017,f5024,f5031,f5038,f5074,f5085,f5092,f5099,f5201,f5208,f5215,f5222,f5229,f5346,f5353,f5360,f5367,f5374,f5483,f5686,f5701,f5816,f6024,f6149,f6158,f6165,f6306,f6313,f6322,f6329,f6336,f6343,f6350,f6460,f7012,f7614,f8268,f8275,f8589,f8596,f8603,f8610,f8617,f8625,f8632,f8639,f8646,f8653,f8662,f8669,f8677,f8699,f8724,f8736,f8751,f8794,f8836,f8843,f8868,f8889,f8898,f9040,f9047,f9202,f10684,f12371,f12917,f12924,f13697,f13707,f13714,f13740,f13751,f14898,f14927,f15442,f15449,f15488,f15495,f15502,f15625,f15633,f15662,f15669,f15679,f15691,f15783,f21915,f21950,f21984,f23791,f24609,f24613])).

fof(f24613,plain,
    ( ~ spl7_6
    | ~ spl7_242
    | spl7_353
    | ~ spl7_358 ),
    inference(avatar_contradiction_clause,[],[f24612])).

fof(f24612,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_242
    | ~ spl7_353
    | ~ spl7_358 ),
    inference(subsumption_resolution,[],[f24611,f649])).

fof(f649,plain,
    ( ! [X2] : v1_funct_2(k1_xboole_0,X2,k1_xboole_0)
    | ~ spl7_6 ),
    inference(superposition,[],[f93,f439])).

fof(f439,plain,
    ( ! [X0] : k1_xboole_0 = sK6(X0,k1_xboole_0)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f422,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',t6_boole)).

fof(f422,plain,
    ( ! [X0] : v1_xboole_0(sK6(X0,k1_xboole_0))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f143,f91,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',cc4_relset_1)).

fof(f91,plain,(
    ! [X0,X1] : m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK6(X0,X1),X0,X1)
      & v1_relat_1(sK6(X0,X1))
      & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK6(X0,X1),X0,X1)
        & v1_relat_1(sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',rc1_funct_2)).

fof(f143,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl7_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f93,plain,(
    ! [X0,X1] : v1_funct_2(sK6(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f71])).

fof(f24611,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_242
    | ~ spl7_353
    | ~ spl7_358 ),
    inference(forward_demodulation,[],[f19562,f6023])).

fof(f6023,plain,
    ( k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0)
    | ~ spl7_242 ),
    inference(avatar_component_clause,[],[f6022])).

fof(f6022,plain,
    ( spl7_242
  <=> k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_242])])).

fof(f19562,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,k1_xboole_0),sK0,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_353
    | ~ spl7_358 ),
    inference(backward_demodulation,[],[f15810,f15668])).

fof(f15668,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),sK0,k1_xboole_0)
    | ~ spl7_353 ),
    inference(avatar_component_clause,[],[f15667])).

fof(f15667,plain,
    ( spl7_353
  <=> ~ v1_funct_2(k5_relat_1(sK3,sK4),sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_353])])).

fof(f15810,plain,
    ( k1_xboole_0 = sK4
    | ~ spl7_6
    | ~ spl7_358 ),
    inference(unit_resulting_resolution,[],[f154,f82,f15782,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1)
      | X1 = X2
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f86,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',t8_boole)).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',t2_subset)).

fof(f15782,plain,
    ( v1_xboole_0(sK4)
    | ~ spl7_358 ),
    inference(avatar_component_clause,[],[f15781])).

fof(f15781,plain,
    ( spl7_358
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_358])])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',existence_m1_subset_1)).

fof(f154,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f143,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',t7_boole)).

fof(f24609,plain,
    ( ~ spl7_6
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_152
    | ~ spl7_158
    | spl7_251
    | spl7_347
    | ~ spl7_358 ),
    inference(avatar_contradiction_clause,[],[f24608])).

fof(f24608,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_152
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_347
    | ~ spl7_358 ),
    inference(subsumption_resolution,[],[f19559,f24515])).

fof(f24515,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_152
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(forward_demodulation,[],[f24514,f1764])).

fof(f1764,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_158 ),
    inference(avatar_component_clause,[],[f1763])).

fof(f1763,plain,
    ( spl7_158
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_158])])).

fof(f24514,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_152
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(forward_demodulation,[],[f24513,f10429])).

fof(f10429,plain,
    ( ! [X0,X1] : k1_xboole_0 = k5_relat_1(sK6(X0,X1),k1_xboole_0)
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f154,f82,f10391,f189])).

fof(f10391,plain,
    ( ! [X0,X1] : v1_xboole_0(k5_relat_1(sK6(X0,X1),k1_xboole_0))
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f10228,f439])).

fof(f10228,plain,
    ( ! [X2,X0,X1] : v1_xboole_0(k5_relat_1(sK6(X0,X1),sK6(X2,k1_xboole_0)))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f143,f1060,f83])).

fof(f1060,plain,(
    ! [X2,X0,X3,X1] : m1_subset_1(k5_relat_1(sK6(X0,X1),sK6(X2,X3)),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ),
    inference(forward_demodulation,[],[f1057,f1013])).

fof(f1013,plain,(
    ! [X2,X0,X3,X1] : k4_relset_1(X0,X1,X2,X3,sK6(X0,X1),sK6(X2,X3)) = k5_relat_1(sK6(X0,X1),sK6(X2,X3)) ),
    inference(unit_resulting_resolution,[],[f91,f91,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',redefinition_k4_relset_1)).

fof(f1057,plain,(
    ! [X2,X0,X3,X1] : m1_subset_1(k4_relset_1(X0,X1,X2,X3,sK6(X0,X1),sK6(X2,X3)),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ),
    inference(unit_resulting_resolution,[],[f91,f91,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',dt_k4_relset_1)).

fof(f24513,plain,
    ( ! [X0,X1] : m1_subset_1(k2_relat_1(k5_relat_1(sK6(X0,X1),k1_xboole_0)),k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_152
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(forward_demodulation,[],[f19384,f21917])).

fof(f21917,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl7_6
    | ~ spl7_152
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(subsumption_resolution,[],[f21916,f1534])).

fof(f1534,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl7_6
    | ~ spl7_152 ),
    inference(backward_demodulation,[],[f1530,f1435])).

fof(f1435,plain,
    ( ! [X0] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0))
    | ~ spl7_6 ),
    inference(superposition,[],[f573,f439])).

fof(f573,plain,(
    ! [X0,X1] : m1_subset_1(k1_relat_1(sK6(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f570,f499])).

fof(f499,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,sK6(X0,X1)) = k1_relat_1(sK6(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f91,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',redefinition_k1_relset_1)).

fof(f570,plain,(
    ! [X0,X1] : m1_subset_1(k1_relset_1(X0,X1,sK6(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f91,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',dt_k1_relset_1)).

fof(f1530,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_152 ),
    inference(unit_resulting_resolution,[],[f1503,f81])).

fof(f1503,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl7_152 ),
    inference(avatar_component_clause,[],[f1502])).

fof(f1502,plain,
    ( spl7_152
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_152])])).

fof(f21916,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl7_6
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(forward_demodulation,[],[f17488,f1764])).

fof(f17488,plain,
    ( ~ m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl7_6
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(backward_demodulation,[],[f15810,f6314])).

fof(f6314,plain,
    ( ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl7_251 ),
    inference(resolution,[],[f6305,f190])).

fof(f190,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,X4)
      | ~ m1_subset_1(X3,X4)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f86,f81])).

fof(f6305,plain,
    ( ~ r2_hidden(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_251 ),
    inference(avatar_component_clause,[],[f6304])).

fof(f6304,plain,
    ( spl7_251
  <=> ~ r2_hidden(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_251])])).

fof(f19384,plain,
    ( ! [X0,X1] : m1_subset_1(k2_relat_1(k5_relat_1(sK6(X0,X1),k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_358 ),
    inference(backward_demodulation,[],[f15810,f15133])).

fof(f15133,plain,
    ( ! [X0,X1] : m1_subset_1(k2_relat_1(k5_relat_1(sK6(X0,X1),sK4)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(backward_demodulation,[],[f226,f6141])).

fof(f6141,plain,
    ( ! [X0,X1] : m1_subset_1(k2_relat_1(k5_relat_1(sK6(X0,X1),sK4)),k1_zfmisc_1(sK2))
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f6035,f6037])).

fof(f6037,plain,
    ( ! [X0,X1] : m1_subset_1(k2_relset_1(X0,sK2,k5_relat_1(sK6(X0,X1),sK4)),k1_zfmisc_1(sK2))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f1068,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',dt_k2_relset_1)).

fof(f1068,plain,
    ( ! [X0,X1] : m1_subset_1(k5_relat_1(sK6(X0,X1),sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f1049,f1005])).

fof(f1005,plain,
    ( ! [X0,X1] : k4_relset_1(X0,X1,sK1,sK2,sK6(X0,X1),sK4) = k5_relat_1(sK6(X0,X1),sK4)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f91,f167,f107])).

fof(f167,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl7_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f1049,plain,
    ( ! [X0,X1] : m1_subset_1(k4_relset_1(X0,X1,sK1,sK2,sK6(X0,X1),sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f91,f167,f108])).

fof(f6035,plain,
    ( ! [X0,X1] : k2_relset_1(X0,sK2,k5_relat_1(sK6(X0,X1),sK4)) = k2_relat_1(k5_relat_1(sK6(X0,X1),sK4))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f1068,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',redefinition_k2_relset_1)).

fof(f226,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl7_24
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f19559,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_347
    | ~ spl7_358 ),
    inference(backward_demodulation,[],[f15810,f15501])).

fof(f15501,plain,
    ( ~ m1_subset_1(sK4,k1_xboole_0)
    | ~ spl7_347 ),
    inference(avatar_component_clause,[],[f15500])).

fof(f15500,plain,
    ( spl7_347
  <=> ~ m1_subset_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_347])])).

fof(f23791,plain,
    ( ~ spl7_6
    | ~ spl7_152
    | spl7_313
    | ~ spl7_358 ),
    inference(avatar_contradiction_clause,[],[f23790])).

fof(f23790,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_152
    | ~ spl7_313
    | ~ spl7_358 ),
    inference(subsumption_resolution,[],[f18506,f1534])).

fof(f18506,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_313
    | ~ spl7_358 ),
    inference(backward_demodulation,[],[f15810,f8842])).

fof(f8842,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_313 ),
    inference(avatar_component_clause,[],[f8841])).

fof(f8841,plain,
    ( spl7_313
  <=> ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_313])])).

fof(f21984,plain,
    ( ~ spl7_6
    | ~ spl7_24
    | ~ spl7_64
    | ~ spl7_152
    | ~ spl7_158
    | spl7_251
    | ~ spl7_358 ),
    inference(avatar_contradiction_clause,[],[f21983])).

fof(f21983,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_64
    | ~ spl7_152
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(subsumption_resolution,[],[f21948,f154])).

fof(f21948,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_64
    | ~ spl7_152
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(backward_demodulation,[],[f21917,f15684])).

fof(f15684,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_24
    | ~ spl7_64 ),
    inference(forward_demodulation,[],[f509,f226])).

fof(f509,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl7_64
  <=> r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f21950,plain,
    ( ~ spl7_6
    | ~ spl7_98
    | ~ spl7_152
    | ~ spl7_158
    | spl7_251
    | spl7_355
    | ~ spl7_358 ),
    inference(avatar_contradiction_clause,[],[f21949])).

fof(f21949,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_98
    | ~ spl7_152
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_355
    | ~ spl7_358 ),
    inference(subsumption_resolution,[],[f21920,f15675])).

fof(f15675,plain,
    ( k1_xboole_0 != sK5(k1_xboole_0)
    | ~ spl7_355 ),
    inference(avatar_component_clause,[],[f15674])).

fof(f15674,plain,
    ( spl7_355
  <=> k1_xboole_0 != sK5(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_355])])).

fof(f21920,plain,
    ( k1_xboole_0 = sK5(k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_98
    | ~ spl7_152
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(backward_demodulation,[],[f21917,f839])).

fof(f839,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_98 ),
    inference(avatar_component_clause,[],[f838])).

fof(f838,plain,
    ( spl7_98
  <=> k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f21915,plain,
    ( ~ spl7_6
    | ~ spl7_24
    | ~ spl7_64
    | ~ spl7_158
    | spl7_251
    | ~ spl7_358 ),
    inference(avatar_contradiction_clause,[],[f21914])).

fof(f21914,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_64
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(subsumption_resolution,[],[f21913,f15684])).

fof(f21913,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_158
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(forward_demodulation,[],[f17487,f1764])).

fof(f17487,plain,
    ( ~ r2_hidden(k2_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_251
    | ~ spl7_358 ),
    inference(backward_demodulation,[],[f15810,f6305])).

fof(f15783,plain,
    ( spl7_358
    | ~ spl7_6
    | ~ spl7_348 ),
    inference(avatar_split_clause,[],[f15746,f15631,f142,f15781])).

fof(f15631,plain,
    ( spl7_348
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_348])])).

fof(f15746,plain,
    ( v1_xboole_0(sK4)
    | ~ spl7_6
    | ~ spl7_348 ),
    inference(unit_resulting_resolution,[],[f82,f154,f15632,f424])).

fof(f424,plain,(
    ! [X4,X2,X5,X3] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | r2_hidden(X5,X4)
      | ~ m1_subset_1(X5,X4) ) ),
    inference(resolution,[],[f83,f86])).

fof(f15632,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl7_348 ),
    inference(avatar_component_clause,[],[f15631])).

fof(f15691,plain,
    ( ~ spl7_357
    | ~ spl7_24
    | spl7_57 ),
    inference(avatar_split_clause,[],[f14941,f470,f225,f15689])).

fof(f15689,plain,
    ( spl7_357
  <=> ~ r2_hidden(k1_xboole_0,sK5(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_357])])).

fof(f470,plain,
    ( spl7_57
  <=> ~ r2_hidden(sK2,sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f14941,plain,
    ( ~ r2_hidden(k1_xboole_0,sK5(k1_xboole_0))
    | ~ spl7_24
    | ~ spl7_57 ),
    inference(backward_demodulation,[],[f226,f471])).

fof(f471,plain,
    ( ~ r2_hidden(sK2,sK5(sK2))
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f470])).

fof(f15679,plain,
    ( spl7_354
    | ~ spl7_6
    | ~ spl7_24
    | spl7_65
    | ~ spl7_98
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f15313,f1502,f838,f511,f225,f142,f15677])).

fof(f15677,plain,
    ( spl7_354
  <=> k1_xboole_0 = sK5(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_354])])).

fof(f511,plain,
    ( spl7_65
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f15313,plain,
    ( k1_xboole_0 = sK5(k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_65
    | ~ spl7_98
    | ~ spl7_152 ),
    inference(backward_demodulation,[],[f15308,f839])).

fof(f15308,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_65
    | ~ spl7_152 ),
    inference(subsumption_resolution,[],[f15042,f1534])).

fof(f15042,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl7_24
    | ~ spl7_65 ),
    inference(backward_demodulation,[],[f226,f5067])).

fof(f5067,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl7_65 ),
    inference(resolution,[],[f190,f512])).

fof(f512,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f511])).

fof(f15669,plain,
    ( ~ spl7_353
    | ~ spl7_24
    | spl7_119 ),
    inference(avatar_split_clause,[],[f14950,f1020,f225,f15667])).

fof(f1020,plain,
    ( spl7_119
  <=> ~ v1_funct_2(k5_relat_1(sK3,sK4),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f14950,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),sK0,k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_119 ),
    inference(backward_demodulation,[],[f226,f1021])).

fof(f1021,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),sK0,sK2)
    | ~ spl7_119 ),
    inference(avatar_component_clause,[],[f1020])).

fof(f15662,plain,
    ( ~ spl7_351
    | spl7_113 ),
    inference(avatar_split_clause,[],[f15623,f958,f15660])).

fof(f15660,plain,
    ( spl7_351
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_351])])).

fof(f958,plain,
    ( spl7_113
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f15623,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK1))
    | ~ spl7_113 ),
    inference(unit_resulting_resolution,[],[f959,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',t1_subset)).

fof(f959,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl7_113 ),
    inference(avatar_component_clause,[],[f958])).

fof(f15633,plain,
    ( spl7_348
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f14936,f225,f166,f15631])).

fof(f14936,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(backward_demodulation,[],[f226,f167])).

fof(f15625,plain,
    ( spl7_106
    | ~ spl7_10
    | ~ spl7_116 ),
    inference(avatar_split_clause,[],[f14928,f995,f159,f924])).

fof(f924,plain,
    ( spl7_106
  <=> k1_relat_1(sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f159,plain,
    ( spl7_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f995,plain,
    ( spl7_116
  <=> k1_relset_1(sK0,sK1,sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f14928,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl7_10
    | ~ spl7_116 ),
    inference(backward_demodulation,[],[f996,f496])).

fof(f496,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f160,f95])).

fof(f160,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f996,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl7_116 ),
    inference(avatar_component_clause,[],[f995])).

fof(f15502,plain,
    ( ~ spl7_347
    | ~ spl7_6
    | ~ spl7_24
    | spl7_65
    | ~ spl7_152
    | spl7_313 ),
    inference(avatar_split_clause,[],[f15327,f8841,f1502,f511,f225,f142,f15500])).

fof(f15327,plain,
    ( ~ m1_subset_1(sK4,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_65
    | ~ spl7_152
    | ~ spl7_313 ),
    inference(backward_demodulation,[],[f15308,f8842])).

fof(f15495,plain,
    ( ~ spl7_345
    | ~ spl7_6
    | ~ spl7_24
    | spl7_65
    | ~ spl7_152
    | spl7_311 ),
    inference(avatar_split_clause,[],[f15326,f8834,f1502,f511,f225,f142,f15493])).

fof(f15493,plain,
    ( spl7_345
  <=> ~ m1_subset_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_345])])).

fof(f8834,plain,
    ( spl7_311
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_311])])).

fof(f15326,plain,
    ( ~ m1_subset_1(sK3,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_65
    | ~ spl7_152
    | ~ spl7_311 ),
    inference(backward_demodulation,[],[f15308,f8835])).

fof(f8835,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_311 ),
    inference(avatar_component_clause,[],[f8834])).

fof(f15488,plain,
    ( spl7_342
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f14935,f225,f132,f15486])).

fof(f15486,plain,
    ( spl7_342
  <=> v1_funct_2(sK4,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_342])])).

fof(f132,plain,
    ( spl7_4
  <=> v1_funct_2(sK4,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f14935,plain,
    ( v1_funct_2(sK4,sK1,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(backward_demodulation,[],[f226,f133])).

fof(f133,plain,
    ( v1_funct_2(sK4,sK1,sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f15449,plain,
    ( ~ spl7_341
    | ~ spl7_6
    | ~ spl7_24
    | spl7_59
    | spl7_65
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f15310,f1502,f511,f477,f225,f142,f15447])).

fof(f15447,plain,
    ( spl7_341
  <=> ~ m1_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_341])])).

fof(f477,plain,
    ( spl7_59
  <=> ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f15310,plain,
    ( ~ m1_subset_1(sK0,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_59
    | ~ spl7_65
    | ~ spl7_152 ),
    inference(backward_demodulation,[],[f15308,f478])).

fof(f478,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f477])).

fof(f15442,plain,
    ( ~ spl7_339
    | ~ spl7_6
    | ~ spl7_24
    | spl7_51
    | spl7_65
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f15309,f1502,f511,f408,f225,f142,f15440])).

fof(f15440,plain,
    ( spl7_339
  <=> ~ m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_339])])).

fof(f408,plain,
    ( spl7_51
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f15309,plain,
    ( ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_51
    | ~ spl7_65
    | ~ spl7_152 ),
    inference(backward_demodulation,[],[f15308,f409])).

fof(f409,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f408])).

fof(f14927,plain,
    ( ~ spl7_6
    | ~ spl7_152
    | spl7_205 ),
    inference(avatar_contradiction_clause,[],[f14926])).

fof(f14926,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_152
    | ~ spl7_205 ),
    inference(subsumption_resolution,[],[f5034,f5006])).

fof(f5006,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl7_6
    | ~ spl7_152 ),
    inference(unit_resulting_resolution,[],[f1534,f1565,f112])).

fof(f112,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
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
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',d1_funct_2)).

fof(f1565,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_152 ),
    inference(forward_demodulation,[],[f1537,f1530])).

fof(f1537,plain,
    ( ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_152 ),
    inference(backward_demodulation,[],[f1530,f1457])).

fof(f1457,plain,
    ( ! [X0,X1] : k1_relset_1(X0,X1,k1_relat_1(k1_xboole_0)) = k1_relat_1(k1_relat_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f1435,f95])).

fof(f5034,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_205 ),
    inference(avatar_component_clause,[],[f5033])).

fof(f5033,plain,
    ( spl7_205
  <=> ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_205])])).

fof(f14898,plain,
    ( ~ spl7_18
    | ~ spl7_26
    | ~ spl7_86
    | spl7_107
    | ~ spl7_160
    | ~ spl7_242
    | ~ spl7_244 ),
    inference(avatar_contradiction_clause,[],[f14897])).

fof(f14897,plain,
    ( $false
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_86
    | ~ spl7_107
    | ~ spl7_160
    | ~ spl7_242
    | ~ spl7_244 ),
    inference(subsumption_resolution,[],[f14896,f6145])).

fof(f6145,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ spl7_244 ),
    inference(avatar_component_clause,[],[f6144])).

fof(f6144,plain,
    ( spl7_244
  <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_244])])).

fof(f14896,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_86
    | ~ spl7_107
    | ~ spl7_160
    | ~ spl7_242 ),
    inference(forward_demodulation,[],[f14895,f1986])).

fof(f1986,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_160 ),
    inference(avatar_component_clause,[],[f1985])).

fof(f1985,plain,
    ( spl7_160
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).

fof(f14895,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k1_xboole_0))
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_86
    | ~ spl7_107
    | ~ spl7_160
    | ~ spl7_242 ),
    inference(subsumption_resolution,[],[f14894,f14893])).

fof(f14893,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | ~ spl7_26
    | ~ spl7_107 ),
    inference(forward_demodulation,[],[f922,f232])).

fof(f232,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl7_26
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f922,plain,
    ( k1_relat_1(sK3) != sK0
    | ~ spl7_107 ),
    inference(avatar_component_clause,[],[f921])).

fof(f921,plain,
    ( spl7_107
  <=> k1_relat_1(sK3) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f14894,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k1_xboole_0))
    | ~ spl7_18
    | ~ spl7_86
    | ~ spl7_160
    | ~ spl7_242 ),
    inference(forward_demodulation,[],[f6028,f1986])).

fof(f6028,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k1_xboole_0))
    | ~ spl7_18
    | ~ spl7_86
    | ~ spl7_242 ),
    inference(subsumption_resolution,[],[f6027,f202])).

fof(f202,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl7_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f6027,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK3)
    | ~ spl7_86
    | ~ spl7_242 ),
    inference(subsumption_resolution,[],[f6025,f656])).

fof(f656,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_86 ),
    inference(avatar_component_clause,[],[f655])).

fof(f655,plain,
    ( spl7_86
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f6025,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_242 ),
    inference(superposition,[],[f80,f6023])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',t46_relat_1)).

fof(f13751,plain,
    ( ~ spl7_10
    | spl7_107
    | ~ spl7_116 ),
    inference(avatar_contradiction_clause,[],[f13750])).

fof(f13750,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_107
    | ~ spl7_116 ),
    inference(subsumption_resolution,[],[f922,f13732])).

fof(f13732,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl7_10
    | ~ spl7_116 ),
    inference(forward_demodulation,[],[f496,f996])).

fof(f13740,plain,
    ( ~ spl7_10
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_84
    | ~ spl7_110
    | ~ spl7_116
    | spl7_337 ),
    inference(avatar_contradiction_clause,[],[f13739])).

fof(f13739,plain,
    ( $false
    | ~ spl7_10
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_84
    | ~ spl7_110
    | ~ spl7_116
    | ~ spl7_337 ),
    inference(subsumption_resolution,[],[f13738,f645])).

fof(f645,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl7_84 ),
    inference(avatar_component_clause,[],[f644])).

fof(f644,plain,
    ( spl7_84
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f13738,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl7_10
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_110
    | ~ spl7_116
    | ~ spl7_337 ),
    inference(forward_demodulation,[],[f13737,f955])).

fof(f955,plain,
    ( k1_relat_1(sK4) = sK1
    | ~ spl7_110 ),
    inference(avatar_component_clause,[],[f954])).

fof(f954,plain,
    ( spl7_110
  <=> k1_relat_1(sK4) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f13737,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl7_10
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_116
    | ~ spl7_337 ),
    inference(subsumption_resolution,[],[f13736,f202])).

fof(f13736,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_116
    | ~ spl7_337 ),
    inference(subsumption_resolution,[],[f13735,f209])).

fof(f209,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl7_20
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f13735,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl7_10
    | ~ spl7_116
    | ~ spl7_337 ),
    inference(subsumption_resolution,[],[f13708,f13732])).

fof(f13708,plain,
    ( k1_relat_1(sK3) != sK0
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl7_337 ),
    inference(superposition,[],[f13706,f80])).

fof(f13706,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK4)) != sK0
    | ~ spl7_337 ),
    inference(avatar_component_clause,[],[f13705])).

fof(f13705,plain,
    ( spl7_337
  <=> k1_relat_1(k5_relat_1(sK3,sK4)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_337])])).

fof(f13714,plain,
    ( ~ spl7_18
    | ~ spl7_20
    | ~ spl7_84
    | ~ spl7_106
    | ~ spl7_110
    | spl7_337 ),
    inference(avatar_contradiction_clause,[],[f13713])).

fof(f13713,plain,
    ( $false
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_84
    | ~ spl7_106
    | ~ spl7_110
    | ~ spl7_337 ),
    inference(subsumption_resolution,[],[f13712,f645])).

fof(f13712,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_106
    | ~ spl7_110
    | ~ spl7_337 ),
    inference(forward_demodulation,[],[f13711,f955])).

fof(f13711,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl7_18
    | ~ spl7_20
    | ~ spl7_106
    | ~ spl7_337 ),
    inference(subsumption_resolution,[],[f13710,f202])).

fof(f13710,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl7_20
    | ~ spl7_106
    | ~ spl7_337 ),
    inference(subsumption_resolution,[],[f13709,f209])).

fof(f13709,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl7_106
    | ~ spl7_337 ),
    inference(subsumption_resolution,[],[f13708,f925])).

fof(f925,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl7_106 ),
    inference(avatar_component_clause,[],[f924])).

fof(f13707,plain,
    ( ~ spl7_337
    | ~ spl7_170
    | spl7_335 ),
    inference(avatar_split_clause,[],[f13700,f13695,f2366,f13705])).

fof(f2366,plain,
    ( spl7_170
  <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_170])])).

fof(f13695,plain,
    ( spl7_335
  <=> k1_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_335])])).

fof(f13700,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK4)) != sK0
    | ~ spl7_170
    | ~ spl7_335 ),
    inference(subsumption_resolution,[],[f13699,f2367])).

fof(f2367,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_170 ),
    inference(avatar_component_clause,[],[f2366])).

fof(f13699,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK4)) != sK0
    | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_335 ),
    inference(superposition,[],[f13696,f95])).

fof(f13696,plain,
    ( k1_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK0
    | ~ spl7_335 ),
    inference(avatar_component_clause,[],[f13695])).

fof(f13697,plain,
    ( ~ spl7_335
    | spl7_25
    | spl7_119
    | ~ spl7_170 ),
    inference(avatar_split_clause,[],[f3221,f2366,f1020,f222,f13695])).

fof(f222,plain,
    ( spl7_25
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f3221,plain,
    ( k1_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK0
    | ~ spl7_25
    | ~ spl7_119
    | ~ spl7_170 ),
    inference(unit_resulting_resolution,[],[f223,f1021,f2367,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f223,plain,
    ( k1_xboole_0 != sK2
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f222])).

fof(f12924,plain,
    ( ~ spl7_333
    | spl7_249 ),
    inference(avatar_split_clause,[],[f6297,f6163,f12922])).

fof(f12922,plain,
    ( spl7_333
  <=> ~ r2_hidden(k2_relat_1(sK3),sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_333])])).

fof(f6163,plain,
    ( spl7_249
  <=> ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_249])])).

fof(f6297,plain,
    ( ~ r2_hidden(k2_relat_1(sK3),sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl7_249 ),
    inference(unit_resulting_resolution,[],[f82,f6164,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',t4_subset)).

fof(f6164,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_249 ),
    inference(avatar_component_clause,[],[f6163])).

fof(f12917,plain,
    ( ~ spl7_331
    | spl7_247 ),
    inference(avatar_split_clause,[],[f6172,f6156,f12915])).

fof(f12915,plain,
    ( spl7_331
  <=> ~ r2_hidden(k2_relat_1(sK4),sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_331])])).

fof(f6156,plain,
    ( spl7_247
  <=> ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_247])])).

fof(f6172,plain,
    ( ~ r2_hidden(k2_relat_1(sK4),sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl7_247 ),
    inference(unit_resulting_resolution,[],[f82,f6157,f105])).

fof(f6157,plain,
    ( ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_247 ),
    inference(avatar_component_clause,[],[f6156])).

fof(f12371,plain,
    ( spl7_328
    | ~ spl7_6
    | ~ spl7_326 ),
    inference(avatar_split_clause,[],[f10721,f10682,f142,f12369])).

fof(f12369,plain,
    ( spl7_328
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_328])])).

fof(f10682,plain,
    ( spl7_326
  <=> v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_326])])).

fof(f10721,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_326 ),
    inference(unit_resulting_resolution,[],[f154,f82,f10683,f189])).

fof(f10683,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_326 ),
    inference(avatar_component_clause,[],[f10682])).

fof(f10684,plain,
    ( spl7_326
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f10437,f142,f10682])).

fof(f10437,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_6 ),
    inference(superposition,[],[f10391,f439])).

fof(f9202,plain,
    ( spl7_324
    | ~ spl7_296 ),
    inference(avatar_split_clause,[],[f9050,f8667,f9200])).

fof(f9200,plain,
    ( spl7_324
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK3,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_324])])).

fof(f8667,plain,
    ( spl7_296
  <=> m1_subset_1(k1_relat_1(k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_296])])).

fof(f9050,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK3,sK3)),sK0)
    | ~ spl7_296 ),
    inference(unit_resulting_resolution,[],[f8668,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',t3_subset)).

fof(f8668,plain,
    ( m1_subset_1(k1_relat_1(k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK0))
    | ~ spl7_296 ),
    inference(avatar_component_clause,[],[f8667])).

fof(f9047,plain,
    ( ~ spl7_323
    | spl7_313 ),
    inference(avatar_split_clause,[],[f8859,f8841,f9045])).

fof(f9045,plain,
    ( spl7_323
  <=> ~ r2_hidden(sK4,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_323])])).

fof(f8859,plain,
    ( ~ r2_hidden(sK4,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl7_313 ),
    inference(unit_resulting_resolution,[],[f82,f8842,f105])).

fof(f9040,plain,
    ( ~ spl7_321
    | spl7_311 ),
    inference(avatar_split_clause,[],[f8850,f8834,f9038])).

fof(f9038,plain,
    ( spl7_321
  <=> ~ r2_hidden(sK3,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_321])])).

fof(f8850,plain,
    ( ~ r2_hidden(sK3,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl7_311 ),
    inference(unit_resulting_resolution,[],[f82,f8835,f105])).

fof(f8898,plain,
    ( spl7_318
    | ~ spl7_294 ),
    inference(avatar_split_clause,[],[f8799,f8660,f8896])).

fof(f8896,plain,
    ( spl7_318
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_318])])).

fof(f8660,plain,
    ( spl7_294
  <=> m1_subset_1(k2_relat_1(k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_294])])).

fof(f8799,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK3)),sK1)
    | ~ spl7_294 ),
    inference(unit_resulting_resolution,[],[f8661,f88])).

fof(f8661,plain,
    ( m1_subset_1(k2_relat_1(k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_294 ),
    inference(avatar_component_clause,[],[f8660])).

fof(f8889,plain,
    ( ~ spl7_317
    | spl7_313 ),
    inference(avatar_split_clause,[],[f8860,f8841,f8887])).

fof(f8887,plain,
    ( spl7_317
  <=> ~ r2_hidden(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_317])])).

fof(f8860,plain,
    ( ~ r2_hidden(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_313 ),
    inference(unit_resulting_resolution,[],[f8842,f85])).

fof(f8868,plain,
    ( ~ spl7_315
    | spl7_311 ),
    inference(avatar_split_clause,[],[f8851,f8834,f8866])).

fof(f8866,plain,
    ( spl7_315
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_315])])).

fof(f8851,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_311 ),
    inference(unit_resulting_resolution,[],[f8835,f85])).

fof(f8843,plain,
    ( ~ spl7_313
    | ~ spl7_6
    | spl7_23
    | spl7_247 ),
    inference(avatar_split_clause,[],[f8825,f6156,f219,f142,f8841])).

fof(f219,plain,
    ( spl7_23
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f8825,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_23
    | ~ spl7_247 ),
    inference(forward_demodulation,[],[f8818,f1869])).

fof(f1869,plain,
    ( ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | ~ spl7_6
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f1791,f81])).

fof(f1791,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f143,f1776,f83])).

fof(f1776,plain,
    ( ! [X1] : m1_subset_1(X1,k1_zfmisc_1(X1))
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f1770,f91])).

fof(f1770,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X1))
        | ~ m1_subset_1(sK6(X1,sK1),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) )
    | ~ spl7_23 ),
    inference(superposition,[],[f97,f852])).

fof(f852,plain,
    ( ! [X0] : k1_relset_1(X0,sK1,sK6(X0,sK1)) = X0
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f220,f93,f91,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f220,plain,
    ( k1_xboole_0 != sK1
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f219])).

fof(f8818,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_247 ),
    inference(unit_resulting_resolution,[],[f6157,f604])).

fof(f604,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f603])).

fof(f603,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f98,f96])).

fof(f8836,plain,
    ( ~ spl7_311
    | ~ spl7_6
    | spl7_23
    | spl7_249 ),
    inference(avatar_split_clause,[],[f8824,f6163,f219,f142,f8834])).

fof(f8824,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_23
    | ~ spl7_249 ),
    inference(forward_demodulation,[],[f8819,f1869])).

fof(f8819,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl7_249 ),
    inference(unit_resulting_resolution,[],[f6164,f604])).

fof(f8794,plain,
    ( spl7_308
    | ~ spl7_290 ),
    inference(avatar_split_clause,[],[f8783,f8644,f8792])).

fof(f8792,plain,
    ( spl7_308
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK4,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_308])])).

fof(f8644,plain,
    ( spl7_290
  <=> m1_subset_1(k1_relat_1(k5_relat_1(sK4,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_290])])).

fof(f8783,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK4,sK3)),sK1)
    | ~ spl7_290 ),
    inference(unit_resulting_resolution,[],[f8645,f88])).

fof(f8645,plain,
    ( m1_subset_1(k1_relat_1(k5_relat_1(sK4,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_290 ),
    inference(avatar_component_clause,[],[f8644])).

fof(f8751,plain,
    ( spl7_306
    | ~ spl7_288 ),
    inference(avatar_split_clause,[],[f8744,f8637,f8749])).

fof(f8749,plain,
    ( spl7_306
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK4,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_306])])).

fof(f8637,plain,
    ( spl7_288
  <=> m1_subset_1(k2_relat_1(k5_relat_1(sK4,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_288])])).

fof(f8744,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK4,sK3)),sK1)
    | ~ spl7_288 ),
    inference(unit_resulting_resolution,[],[f8638,f88])).

fof(f8638,plain,
    ( m1_subset_1(k2_relat_1(k5_relat_1(sK4,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_288 ),
    inference(avatar_component_clause,[],[f8637])).

fof(f8736,plain,
    ( spl7_304
    | ~ spl7_284 ),
    inference(avatar_split_clause,[],[f8725,f8623,f8734])).

fof(f8734,plain,
    ( spl7_304
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK3,sK4)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_304])])).

fof(f8623,plain,
    ( spl7_284
  <=> m1_subset_1(k1_relat_1(k5_relat_1(sK3,sK4)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_284])])).

fof(f8725,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK3,sK4)),sK0)
    | ~ spl7_284 ),
    inference(unit_resulting_resolution,[],[f8624,f88])).

fof(f8624,plain,
    ( m1_subset_1(k1_relat_1(k5_relat_1(sK3,sK4)),k1_zfmisc_1(sK0))
    | ~ spl7_284 ),
    inference(avatar_component_clause,[],[f8623])).

fof(f8724,plain,
    ( spl7_302
    | ~ spl7_282 ),
    inference(avatar_split_clause,[],[f8717,f8615,f8722])).

fof(f8722,plain,
    ( spl7_302
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_302])])).

fof(f8615,plain,
    ( spl7_282
  <=> m1_subset_1(k2_relat_1(k5_relat_1(sK3,sK4)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_282])])).

fof(f8717,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),sK2)
    | ~ spl7_282 ),
    inference(unit_resulting_resolution,[],[f8616,f88])).

fof(f8616,plain,
    ( m1_subset_1(k2_relat_1(k5_relat_1(sK3,sK4)),k1_zfmisc_1(sK2))
    | ~ spl7_282 ),
    inference(avatar_component_clause,[],[f8615])).

fof(f8699,plain,
    ( spl7_300
    | ~ spl7_278 ),
    inference(avatar_split_clause,[],[f8688,f8601,f8697])).

fof(f8697,plain,
    ( spl7_300
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK4,sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_300])])).

fof(f8601,plain,
    ( spl7_278
  <=> m1_subset_1(k1_relat_1(k5_relat_1(sK4,sK4)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_278])])).

fof(f8688,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK4,sK4)),sK1)
    | ~ spl7_278 ),
    inference(unit_resulting_resolution,[],[f8602,f88])).

fof(f8602,plain,
    ( m1_subset_1(k1_relat_1(k5_relat_1(sK4,sK4)),k1_zfmisc_1(sK1))
    | ~ spl7_278 ),
    inference(avatar_component_clause,[],[f8601])).

fof(f8677,plain,
    ( spl7_298
    | ~ spl7_276 ),
    inference(avatar_split_clause,[],[f8670,f8594,f8675])).

fof(f8675,plain,
    ( spl7_298
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK4,sK4)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_298])])).

fof(f8594,plain,
    ( spl7_276
  <=> m1_subset_1(k2_relat_1(k5_relat_1(sK4,sK4)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_276])])).

fof(f8670,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK4,sK4)),sK2)
    | ~ spl7_276 ),
    inference(unit_resulting_resolution,[],[f8595,f88])).

fof(f8595,plain,
    ( m1_subset_1(k2_relat_1(k5_relat_1(sK4,sK4)),k1_zfmisc_1(sK2))
    | ~ spl7_276 ),
    inference(avatar_component_clause,[],[f8594])).

fof(f8669,plain,
    ( spl7_296
    | ~ spl7_174 ),
    inference(avatar_split_clause,[],[f3937,f2896,f8667])).

fof(f2896,plain,
    ( spl7_174
  <=> m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_174])])).

fof(f3937,plain,
    ( m1_subset_1(k1_relat_1(k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK0))
    | ~ spl7_174 ),
    inference(backward_demodulation,[],[f3860,f3862])).

fof(f3862,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK0))
    | ~ spl7_174 ),
    inference(unit_resulting_resolution,[],[f2897,f97])).

fof(f2897,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_174 ),
    inference(avatar_component_clause,[],[f2896])).

fof(f3860,plain,
    ( k1_relset_1(sK0,sK1,k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_174 ),
    inference(unit_resulting_resolution,[],[f2897,f95])).

fof(f8662,plain,
    ( spl7_294
    | ~ spl7_174 ),
    inference(avatar_split_clause,[],[f3936,f2896,f8660])).

fof(f3936,plain,
    ( m1_subset_1(k2_relat_1(k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_174 ),
    inference(backward_demodulation,[],[f3861,f3863])).

fof(f3863,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,k5_relat_1(sK3,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_174 ),
    inference(unit_resulting_resolution,[],[f2897,f98])).

fof(f3861,plain,
    ( k2_relset_1(sK0,sK1,k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_174 ),
    inference(unit_resulting_resolution,[],[f2897,f96])).

fof(f8653,plain,
    ( spl7_292
    | ~ spl7_174 ),
    inference(avatar_split_clause,[],[f3912,f2896,f8651])).

fof(f8651,plain,
    ( spl7_292
  <=> r1_tarski(k5_relat_1(sK3,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_292])])).

fof(f3912,plain,
    ( r1_tarski(k5_relat_1(sK3,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl7_174 ),
    inference(unit_resulting_resolution,[],[f2897,f88])).

fof(f8646,plain,
    ( spl7_290
    | ~ spl7_172 ),
    inference(avatar_split_clause,[],[f3458,f2638,f8644])).

fof(f2638,plain,
    ( spl7_172
  <=> m1_subset_1(k5_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).

fof(f3458,plain,
    ( m1_subset_1(k1_relat_1(k5_relat_1(sK4,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_172 ),
    inference(backward_demodulation,[],[f3387,f3389])).

fof(f3389,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK1,k5_relat_1(sK4,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_172 ),
    inference(unit_resulting_resolution,[],[f2639,f97])).

fof(f2639,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_172 ),
    inference(avatar_component_clause,[],[f2638])).

fof(f3387,plain,
    ( k1_relset_1(sK1,sK1,k5_relat_1(sK4,sK3)) = k1_relat_1(k5_relat_1(sK4,sK3))
    | ~ spl7_172 ),
    inference(unit_resulting_resolution,[],[f2639,f95])).

fof(f8639,plain,
    ( spl7_288
    | ~ spl7_172 ),
    inference(avatar_split_clause,[],[f3457,f2638,f8637])).

fof(f3457,plain,
    ( m1_subset_1(k2_relat_1(k5_relat_1(sK4,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_172 ),
    inference(backward_demodulation,[],[f3388,f3390])).

fof(f3390,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK1,k5_relat_1(sK4,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_172 ),
    inference(unit_resulting_resolution,[],[f2639,f98])).

fof(f3388,plain,
    ( k2_relset_1(sK1,sK1,k5_relat_1(sK4,sK3)) = k2_relat_1(k5_relat_1(sK4,sK3))
    | ~ spl7_172 ),
    inference(unit_resulting_resolution,[],[f2639,f96])).

fof(f8632,plain,
    ( spl7_286
    | ~ spl7_172 ),
    inference(avatar_split_clause,[],[f3435,f2638,f8630])).

fof(f8630,plain,
    ( spl7_286
  <=> r1_tarski(k5_relat_1(sK4,sK3),k2_zfmisc_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_286])])).

fof(f3435,plain,
    ( r1_tarski(k5_relat_1(sK4,sK3),k2_zfmisc_1(sK1,sK1))
    | ~ spl7_172 ),
    inference(unit_resulting_resolution,[],[f2639,f88])).

fof(f8625,plain,
    ( spl7_284
    | ~ spl7_170 ),
    inference(avatar_split_clause,[],[f3283,f2366,f8623])).

fof(f3283,plain,
    ( m1_subset_1(k1_relat_1(k5_relat_1(sK3,sK4)),k1_zfmisc_1(sK0))
    | ~ spl7_170 ),
    inference(backward_demodulation,[],[f3217,f3219])).

fof(f3219,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)),k1_zfmisc_1(sK0))
    | ~ spl7_170 ),
    inference(unit_resulting_resolution,[],[f2367,f97])).

fof(f3217,plain,
    ( k1_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl7_170 ),
    inference(unit_resulting_resolution,[],[f2367,f95])).

fof(f8617,plain,
    ( spl7_282
    | ~ spl7_170 ),
    inference(avatar_split_clause,[],[f3282,f2366,f8615])).

fof(f3282,plain,
    ( m1_subset_1(k2_relat_1(k5_relat_1(sK3,sK4)),k1_zfmisc_1(sK2))
    | ~ spl7_170 ),
    inference(backward_demodulation,[],[f3218,f3220])).

fof(f3220,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)),k1_zfmisc_1(sK2))
    | ~ spl7_170 ),
    inference(unit_resulting_resolution,[],[f2367,f98])).

fof(f3218,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl7_170 ),
    inference(unit_resulting_resolution,[],[f2367,f96])).

fof(f8610,plain,
    ( spl7_280
    | ~ spl7_170 ),
    inference(avatar_split_clause,[],[f3262,f2366,f8608])).

fof(f8608,plain,
    ( spl7_280
  <=> r1_tarski(k5_relat_1(sK3,sK4),k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_280])])).

fof(f3262,plain,
    ( r1_tarski(k5_relat_1(sK3,sK4),k2_zfmisc_1(sK0,sK2))
    | ~ spl7_170 ),
    inference(unit_resulting_resolution,[],[f2367,f88])).

fof(f8603,plain,
    ( spl7_278
    | ~ spl7_168 ),
    inference(avatar_split_clause,[],[f3180,f2179,f8601])).

fof(f2179,plain,
    ( spl7_168
  <=> m1_subset_1(k5_relat_1(sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_168])])).

fof(f3180,plain,
    ( m1_subset_1(k1_relat_1(k5_relat_1(sK4,sK4)),k1_zfmisc_1(sK1))
    | ~ spl7_168 ),
    inference(backward_demodulation,[],[f3121,f3123])).

fof(f3123,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,k5_relat_1(sK4,sK4)),k1_zfmisc_1(sK1))
    | ~ spl7_168 ),
    inference(unit_resulting_resolution,[],[f2180,f97])).

fof(f2180,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_168 ),
    inference(avatar_component_clause,[],[f2179])).

fof(f3121,plain,
    ( k1_relset_1(sK1,sK2,k5_relat_1(sK4,sK4)) = k1_relat_1(k5_relat_1(sK4,sK4))
    | ~ spl7_168 ),
    inference(unit_resulting_resolution,[],[f2180,f95])).

fof(f8596,plain,
    ( spl7_276
    | ~ spl7_168 ),
    inference(avatar_split_clause,[],[f3179,f2179,f8594])).

fof(f3179,plain,
    ( m1_subset_1(k2_relat_1(k5_relat_1(sK4,sK4)),k1_zfmisc_1(sK2))
    | ~ spl7_168 ),
    inference(backward_demodulation,[],[f3122,f3124])).

fof(f3124,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK2,k5_relat_1(sK4,sK4)),k1_zfmisc_1(sK2))
    | ~ spl7_168 ),
    inference(unit_resulting_resolution,[],[f2180,f98])).

fof(f3122,plain,
    ( k2_relset_1(sK1,sK2,k5_relat_1(sK4,sK4)) = k2_relat_1(k5_relat_1(sK4,sK4))
    | ~ spl7_168 ),
    inference(unit_resulting_resolution,[],[f2180,f96])).

fof(f8589,plain,
    ( spl7_274
    | ~ spl7_168 ),
    inference(avatar_split_clause,[],[f3161,f2179,f8587])).

fof(f8587,plain,
    ( spl7_274
  <=> r1_tarski(k5_relat_1(sK4,sK4),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_274])])).

fof(f3161,plain,
    ( r1_tarski(k5_relat_1(sK4,sK4),k2_zfmisc_1(sK1,sK2))
    | ~ spl7_168 ),
    inference(unit_resulting_resolution,[],[f2180,f88])).

fof(f8275,plain,
    ( spl7_272
    | ~ spl7_86
    | ~ spl7_96 ),
    inference(avatar_split_clause,[],[f815,f799,f655,f8273])).

fof(f8273,plain,
    ( spl7_272
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_272])])).

fof(f799,plain,
    ( spl7_96
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f815,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_86
    | ~ spl7_96 ),
    inference(unit_resulting_resolution,[],[f656,f800,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',dt_k5_relat_1)).

fof(f800,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_96 ),
    inference(avatar_component_clause,[],[f799])).

fof(f8268,plain,
    ( spl7_270
    | ~ spl7_86
    | ~ spl7_96 ),
    inference(avatar_split_clause,[],[f802,f799,f655,f8266])).

fof(f8266,plain,
    ( spl7_270
  <=> v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_270])])).

fof(f802,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0))
    | ~ spl7_86
    | ~ spl7_96 ),
    inference(unit_resulting_resolution,[],[f656,f800,f87])).

fof(f7614,plain,
    ( spl7_268
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f1003,f166,f7612])).

fof(f7612,plain,
    ( spl7_268
  <=> k4_relset_1(sK1,sK2,sK1,sK2,sK4,sK4) = k5_relat_1(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_268])])).

fof(f1003,plain,
    ( k4_relset_1(sK1,sK2,sK1,sK2,sK4,sK4) = k5_relat_1(sK4,sK4)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f167,f107])).

fof(f7012,plain,
    ( spl7_266
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f1002,f166,f159,f7010])).

fof(f7010,plain,
    ( spl7_266
  <=> k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_266])])).

fof(f1002,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f160,f167,f107])).

fof(f6460,plain,
    ( spl7_264
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f999,f166,f159,f6458])).

fof(f6458,plain,
    ( spl7_264
  <=> k4_relset_1(sK1,sK2,sK0,sK1,sK4,sK3) = k5_relat_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_264])])).

fof(f999,plain,
    ( k4_relset_1(sK1,sK2,sK0,sK1,sK4,sK3) = k5_relat_1(sK4,sK3)
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f160,f107])).

fof(f6350,plain,
    ( spl7_262
    | ~ spl7_20
    | ~ spl7_96 ),
    inference(avatar_split_clause,[],[f826,f799,f208,f6348])).

fof(f6348,plain,
    ( spl7_262
  <=> v1_relat_1(k5_relat_1(sK4,k5_relat_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_262])])).

fof(f826,plain,
    ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_20
    | ~ spl7_96 ),
    inference(unit_resulting_resolution,[],[f209,f800,f87])).

fof(f6343,plain,
    ( spl7_260
    | ~ spl7_18
    | ~ spl7_96 ),
    inference(avatar_split_clause,[],[f825,f799,f201,f6341])).

fof(f6341,plain,
    ( spl7_260
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_260])])).

fof(f825,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_18
    | ~ spl7_96 ),
    inference(unit_resulting_resolution,[],[f202,f800,f87])).

fof(f6336,plain,
    ( spl7_258
    | ~ spl7_20
    | ~ spl7_96 ),
    inference(avatar_split_clause,[],[f813,f799,f208,f6334])).

fof(f6334,plain,
    ( spl7_258
  <=> v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_258])])).

fof(f813,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),sK4))
    | ~ spl7_20
    | ~ spl7_96 ),
    inference(unit_resulting_resolution,[],[f209,f800,f87])).

fof(f6329,plain,
    ( spl7_256
    | ~ spl7_18
    | ~ spl7_96 ),
    inference(avatar_split_clause,[],[f812,f799,f201,f6327])).

fof(f6327,plain,
    ( spl7_256
  <=> v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_256])])).

fof(f812,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),sK3))
    | ~ spl7_18
    | ~ spl7_96 ),
    inference(unit_resulting_resolution,[],[f202,f800,f87])).

fof(f6322,plain,
    ( spl7_254
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f998,f159,f6320])).

fof(f6320,plain,
    ( spl7_254
  <=> k4_relset_1(sK0,sK1,sK0,sK1,sK3,sK3) = k5_relat_1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_254])])).

fof(f998,plain,
    ( k4_relset_1(sK0,sK1,sK0,sK1,sK3,sK3) = k5_relat_1(sK3,sK3)
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f160,f160,f107])).

fof(f6313,plain,
    ( ~ spl7_253
    | spl7_249 ),
    inference(avatar_split_clause,[],[f6298,f6163,f6311])).

fof(f6311,plain,
    ( spl7_253
  <=> ~ r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_253])])).

fof(f6298,plain,
    ( ~ r2_hidden(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_249 ),
    inference(unit_resulting_resolution,[],[f6164,f85])).

fof(f6306,plain,
    ( ~ spl7_251
    | spl7_247 ),
    inference(avatar_split_clause,[],[f6173,f6156,f6304])).

fof(f6173,plain,
    ( ~ r2_hidden(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_247 ),
    inference(unit_resulting_resolution,[],[f6157,f85])).

fof(f6165,plain,
    ( ~ spl7_249
    | spl7_245 ),
    inference(avatar_split_clause,[],[f6150,f6147,f6163])).

fof(f6147,plain,
    ( spl7_245
  <=> ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_245])])).

fof(f6150,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_245 ),
    inference(unit_resulting_resolution,[],[f6148,f88])).

fof(f6148,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ spl7_245 ),
    inference(avatar_component_clause,[],[f6147])).

fof(f6158,plain,
    ( ~ spl7_247
    | spl7_239 ),
    inference(avatar_split_clause,[],[f6016,f5699,f6156])).

fof(f5699,plain,
    ( spl7_239
  <=> ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_239])])).

fof(f6016,plain,
    ( ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_239 ),
    inference(unit_resulting_resolution,[],[f5700,f88])).

fof(f5700,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0)
    | ~ spl7_239 ),
    inference(avatar_component_clause,[],[f5699])).

fof(f6149,plain,
    ( ~ spl7_245
    | ~ spl7_18
    | spl7_27
    | ~ spl7_86
    | ~ spl7_106
    | ~ spl7_160
    | ~ spl7_242 ),
    inference(avatar_split_clause,[],[f6032,f6022,f1985,f924,f655,f228,f201,f6147])).

fof(f228,plain,
    ( spl7_27
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f6032,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ spl7_18
    | ~ spl7_27
    | ~ spl7_86
    | ~ spl7_106
    | ~ spl7_160
    | ~ spl7_242 ),
    inference(forward_demodulation,[],[f6031,f1986])).

fof(f6031,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k1_xboole_0))
    | ~ spl7_18
    | ~ spl7_27
    | ~ spl7_86
    | ~ spl7_106
    | ~ spl7_160
    | ~ spl7_242 ),
    inference(subsumption_resolution,[],[f6030,f229])).

fof(f229,plain,
    ( k1_xboole_0 != sK0
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f228])).

fof(f6030,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k1_xboole_0))
    | ~ spl7_18
    | ~ spl7_86
    | ~ spl7_106
    | ~ spl7_160
    | ~ spl7_242 ),
    inference(forward_demodulation,[],[f6029,f1986])).

fof(f6029,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(k1_xboole_0))
    | ~ spl7_18
    | ~ spl7_86
    | ~ spl7_106
    | ~ spl7_242 ),
    inference(forward_demodulation,[],[f6028,f925])).

fof(f6024,plain,
    ( spl7_242
    | ~ spl7_6
    | ~ spl7_240 ),
    inference(avatar_split_clause,[],[f5833,f5814,f142,f6022])).

fof(f5814,plain,
    ( spl7_240
  <=> v1_xboole_0(k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_240])])).

fof(f5833,plain,
    ( k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_240 ),
    inference(unit_resulting_resolution,[],[f143,f5815,f89])).

fof(f5815,plain,
    ( v1_xboole_0(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl7_240 ),
    inference(avatar_component_clause,[],[f5814])).

fof(f5816,plain,
    ( spl7_240
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f5808,f159,f142,f5814])).

fof(f5808,plain,
    ( v1_xboole_0(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f5702,f439])).

fof(f5702,plain,
    ( ! [X0] : v1_xboole_0(k5_relat_1(sK3,sK6(X0,k1_xboole_0)))
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f143,f1063,f83])).

fof(f1063,plain,
    ( ! [X0,X1] : m1_subset_1(k5_relat_1(sK3,sK6(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f1054,f1010])).

fof(f1010,plain,
    ( ! [X0,X1] : k4_relset_1(sK0,sK1,X0,X1,sK3,sK6(X0,X1)) = k5_relat_1(sK3,sK6(X0,X1))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f160,f91,f107])).

fof(f1054,plain,
    ( ! [X0,X1] : m1_subset_1(k4_relset_1(sK0,sK1,X0,X1,sK3,sK6(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f160,f91,f108])).

fof(f5701,plain,
    ( ~ spl7_239
    | ~ spl7_20
    | spl7_23
    | ~ spl7_86
    | ~ spl7_110
    | ~ spl7_160
    | ~ spl7_236 ),
    inference(avatar_split_clause,[],[f5694,f5684,f1985,f954,f655,f219,f208,f5699])).

fof(f5684,plain,
    ( spl7_236
  <=> k1_xboole_0 = k5_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_236])])).

fof(f5694,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_xboole_0)
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_86
    | ~ spl7_110
    | ~ spl7_160
    | ~ spl7_236 ),
    inference(forward_demodulation,[],[f5693,f1986])).

fof(f5693,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(k1_xboole_0))
    | ~ spl7_20
    | ~ spl7_23
    | ~ spl7_86
    | ~ spl7_110
    | ~ spl7_160
    | ~ spl7_236 ),
    inference(subsumption_resolution,[],[f5692,f220])).

fof(f5692,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(k1_xboole_0))
    | ~ spl7_20
    | ~ spl7_86
    | ~ spl7_110
    | ~ spl7_160
    | ~ spl7_236 ),
    inference(forward_demodulation,[],[f5691,f1986])).

fof(f5691,plain,
    ( k1_relat_1(k1_xboole_0) = sK1
    | ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(k1_xboole_0))
    | ~ spl7_20
    | ~ spl7_86
    | ~ spl7_110
    | ~ spl7_236 ),
    inference(forward_demodulation,[],[f5690,f955])).

fof(f5690,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK4)
    | ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(k1_xboole_0))
    | ~ spl7_20
    | ~ spl7_86
    | ~ spl7_236 ),
    inference(subsumption_resolution,[],[f5689,f209])).

fof(f5689,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK4)
    | ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK4)
    | ~ spl7_86
    | ~ spl7_236 ),
    inference(subsumption_resolution,[],[f5687,f656])).

fof(f5687,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK4)
    | ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK4)
    | ~ spl7_236 ),
    inference(superposition,[],[f80,f5685])).

fof(f5685,plain,
    ( k1_xboole_0 = k5_relat_1(sK4,k1_xboole_0)
    | ~ spl7_236 ),
    inference(avatar_component_clause,[],[f5684])).

fof(f5686,plain,
    ( spl7_236
    | ~ spl7_6
    | ~ spl7_234 ),
    inference(avatar_split_clause,[],[f5499,f5481,f142,f5684])).

fof(f5481,plain,
    ( spl7_234
  <=> v1_xboole_0(k5_relat_1(sK4,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_234])])).

fof(f5499,plain,
    ( k1_xboole_0 = k5_relat_1(sK4,k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_234 ),
    inference(unit_resulting_resolution,[],[f143,f5482,f89])).

fof(f5482,plain,
    ( v1_xboole_0(k5_relat_1(sK4,k1_xboole_0))
    | ~ spl7_234 ),
    inference(avatar_component_clause,[],[f5481])).

fof(f5483,plain,
    ( spl7_234
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f5475,f166,f142,f5481])).

fof(f5475,plain,
    ( v1_xboole_0(k5_relat_1(sK4,k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f5375,f439])).

fof(f5375,plain,
    ( ! [X0] : v1_xboole_0(k5_relat_1(sK4,sK6(X0,k1_xboole_0)))
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f143,f1062,f83])).

fof(f1062,plain,
    ( ! [X0,X1] : m1_subset_1(k5_relat_1(sK4,sK6(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f1055,f1011])).

fof(f1011,plain,
    ( ! [X0,X1] : k4_relset_1(sK1,sK2,X0,X1,sK4,sK6(X0,X1)) = k5_relat_1(sK4,sK6(X0,X1))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f91,f107])).

fof(f1055,plain,
    ( ! [X0,X1] : m1_subset_1(k4_relset_1(sK1,sK2,X0,X1,sK4,sK6(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f91,f108])).

fof(f5374,plain,
    ( spl7_232
    | ~ spl7_86
    | ~ spl7_92 ),
    inference(avatar_split_clause,[],[f749,f699,f655,f5372])).

fof(f5372,plain,
    ( spl7_232
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_232])])).

fof(f699,plain,
    ( spl7_92
  <=> v1_relat_1(k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f749,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0))
    | ~ spl7_86
    | ~ spl7_92 ),
    inference(unit_resulting_resolution,[],[f656,f700,f87])).

fof(f700,plain,
    ( v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f699])).

fof(f5367,plain,
    ( spl7_230
    | ~ spl7_20
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f747,f692,f208,f5365])).

fof(f5365,plain,
    ( spl7_230
  <=> v1_relat_1(k5_relat_1(sK4,k5_relat_1(k1_xboole_0,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_230])])).

fof(f692,plain,
    ( spl7_90
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f747,plain,
    ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(k1_xboole_0,sK4)))
    | ~ spl7_20
    | ~ spl7_90 ),
    inference(unit_resulting_resolution,[],[f209,f693,f87])).

fof(f693,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK4))
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f692])).

fof(f5360,plain,
    ( spl7_228
    | ~ spl7_18
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f746,f692,f201,f5358])).

fof(f5358,plain,
    ( spl7_228
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_228])])).

fof(f746,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK4)))
    | ~ spl7_18
    | ~ spl7_90 ),
    inference(unit_resulting_resolution,[],[f202,f693,f87])).

fof(f5353,plain,
    ( spl7_226
    | ~ spl7_86
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f739,f692,f655,f5351])).

fof(f5351,plain,
    ( spl7_226
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_226])])).

fof(f739,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK4)))
    | ~ spl7_86
    | ~ spl7_90 ),
    inference(unit_resulting_resolution,[],[f656,f693,f87])).

fof(f5346,plain,
    ( spl7_224
    | ~ spl7_20
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f737,f692,f208,f5344])).

fof(f5344,plain,
    ( spl7_224
  <=> v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_224])])).

fof(f737,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK4),sK4))
    | ~ spl7_20
    | ~ spl7_90 ),
    inference(unit_resulting_resolution,[],[f209,f693,f87])).

fof(f5229,plain,
    ( spl7_222
    | ~ spl7_18
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f736,f692,f201,f5227])).

fof(f5227,plain,
    ( spl7_222
  <=> v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_222])])).

fof(f736,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK4),sK3))
    | ~ spl7_18
    | ~ spl7_90 ),
    inference(unit_resulting_resolution,[],[f202,f693,f87])).

fof(f5222,plain,
    ( spl7_220
    | ~ spl7_86
    | ~ spl7_90 ),
    inference(avatar_split_clause,[],[f729,f692,f655,f5220])).

fof(f5220,plain,
    ( spl7_220
  <=> v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK4),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_220])])).

fof(f729,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK4),k1_xboole_0))
    | ~ spl7_86
    | ~ spl7_90 ),
    inference(unit_resulting_resolution,[],[f656,f693,f87])).

fof(f5215,plain,
    ( spl7_218
    | ~ spl7_20
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f725,f685,f208,f5213])).

fof(f5213,plain,
    ( spl7_218
  <=> v1_relat_1(k5_relat_1(sK4,k5_relat_1(k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).

fof(f685,plain,
    ( spl7_88
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f725,plain,
    ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(k1_xboole_0,sK3)))
    | ~ spl7_20
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f209,f686,f87])).

fof(f686,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f685])).

fof(f5208,plain,
    ( spl7_216
    | ~ spl7_18
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f724,f685,f201,f5206])).

fof(f5206,plain,
    ( spl7_216
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_216])])).

fof(f724,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK3)))
    | ~ spl7_18
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f202,f686,f87])).

fof(f5201,plain,
    ( spl7_214
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f718,f685,f655,f5199])).

fof(f5199,plain,
    ( spl7_214
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_214])])).

fof(f718,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK3)))
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f656,f686,f87])).

fof(f5099,plain,
    ( spl7_212
    | ~ spl7_20
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f716,f685,f208,f5097])).

fof(f5097,plain,
    ( spl7_212
  <=> v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_212])])).

fof(f716,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK4))
    | ~ spl7_20
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f209,f686,f87])).

fof(f5092,plain,
    ( spl7_210
    | ~ spl7_18
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f715,f685,f201,f5090])).

fof(f5090,plain,
    ( spl7_210
  <=> v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_210])])).

fof(f715,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK3))
    | ~ spl7_18
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f202,f686,f87])).

fof(f5085,plain,
    ( spl7_208
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f709,f685,f655,f5083])).

fof(f5083,plain,
    ( spl7_208
  <=> v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK3),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_208])])).

fof(f709,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,sK3),k1_xboole_0))
    | ~ spl7_86
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f656,f686,f87])).

fof(f5074,plain,
    ( spl7_206
    | ~ spl7_6
    | ~ spl7_86
    | ~ spl7_160 ),
    inference(avatar_split_clause,[],[f2125,f1985,f655,f142,f5072])).

fof(f5072,plain,
    ( spl7_206
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_206])])).

fof(f2125,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_86
    | ~ spl7_160 ),
    inference(forward_demodulation,[],[f2124,f1986])).

fof(f2124,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_86
    | ~ spl7_160 ),
    inference(forward_demodulation,[],[f2123,f439])).

fof(f2123,plain,
    ( ! [X0] : k1_relat_1(sK6(X0,k1_xboole_0)) = k1_relat_1(k5_relat_1(sK6(X0,k1_xboole_0),k1_xboole_0))
    | ~ spl7_86
    | ~ spl7_160 ),
    inference(forward_demodulation,[],[f2100,f1986])).

fof(f2100,plain,
    ( ! [X0] : k1_relat_1(sK6(X0,k1_relat_1(k1_xboole_0))) = k1_relat_1(k5_relat_1(sK6(X0,k1_relat_1(k1_xboole_0)),k1_xboole_0))
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f656,f92,f1593,f80])).

fof(f1593,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(sK6(X0,X1)),X1) ),
    inference(unit_resulting_resolution,[],[f605,f88])).

fof(f605,plain,(
    ! [X0,X1] : m1_subset_1(k2_relat_1(sK6(X0,X1)),k1_zfmisc_1(X1)) ),
    inference(forward_demodulation,[],[f602,f524])).

fof(f524,plain,(
    ! [X0,X1] : k2_relset_1(X0,X1,sK6(X0,X1)) = k2_relat_1(sK6(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f91,f96])).

fof(f602,plain,(
    ! [X0,X1] : m1_subset_1(k2_relset_1(X0,X1,sK6(X0,X1)),k1_zfmisc_1(X1)) ),
    inference(unit_resulting_resolution,[],[f91,f98])).

fof(f92,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f71])).

fof(f5038,plain,
    ( spl7_204
    | ~ spl7_6
    | spl7_25
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f5009,f1502,f222,f142,f5036])).

fof(f5036,plain,
    ( spl7_204
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_204])])).

fof(f5009,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl7_6
    | ~ spl7_25
    | ~ spl7_152 ),
    inference(unit_resulting_resolution,[],[f223,f1534,f1565,f101])).

fof(f5031,plain,
    ( spl7_202
    | ~ spl7_6
    | spl7_27
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f5008,f1502,f228,f142,f5029])).

fof(f5029,plain,
    ( spl7_202
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_202])])).

fof(f5008,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl7_6
    | ~ spl7_27
    | ~ spl7_152 ),
    inference(unit_resulting_resolution,[],[f229,f1534,f1565,f101])).

fof(f5024,plain,
    ( spl7_200
    | ~ spl7_6
    | spl7_23
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f5007,f1502,f219,f142,f5022])).

fof(f5022,plain,
    ( spl7_200
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_200])])).

fof(f5007,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl7_6
    | ~ spl7_23
    | ~ spl7_152 ),
    inference(unit_resulting_resolution,[],[f220,f1534,f1565,f101])).

fof(f5017,plain,
    ( spl7_24
    | spl7_120
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f875,f166,f132,f1027,f225])).

fof(f1027,plain,
    ( spl7_120
  <=> k1_relset_1(sK1,sK2,sK4) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f875,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f858,f167])).

fof(f858,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_4 ),
    inference(resolution,[],[f99,f133])).

fof(f5005,plain,
    ( spl7_198
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f833,f142,f5003])).

fof(f5003,plain,
    ( spl7_198
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_198])])).

fof(f833,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f829,f648])).

fof(f648,plain,
    ( ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ spl7_6 ),
    inference(superposition,[],[f91,f439])).

fof(f829,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_6 ),
    inference(resolution,[],[f113,f649])).

fof(f113,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f3311,plain,
    ( ~ spl7_197
    | spl7_55 ),
    inference(avatar_split_clause,[],[f976,f463,f3309])).

fof(f3309,plain,
    ( spl7_197
  <=> ~ r2_hidden(sK2,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_197])])).

fof(f463,plain,
    ( spl7_55
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f976,plain,
    ( ~ r2_hidden(sK2,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f82,f464,f105])).

fof(f464,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f463])).

fof(f3304,plain,
    ( spl7_194
    | ~ spl7_40
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f670,f655,f302,f3302])).

fof(f3302,plain,
    ( spl7_194
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK4),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_194])])).

fof(f302,plain,
    ( spl7_40
  <=> v1_relat_1(k5_relat_1(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f670,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK4),k1_xboole_0))
    | ~ spl7_40
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f303,f656,f87])).

fof(f303,plain,
    ( v1_relat_1(k5_relat_1(sK4,sK4))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f302])).

fof(f3297,plain,
    ( spl7_192
    | ~ spl7_38
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f669,f655,f295,f3295])).

fof(f3295,plain,
    ( spl7_192
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_192])])).

fof(f295,plain,
    ( spl7_38
  <=> v1_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f669,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),k1_xboole_0))
    | ~ spl7_38
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f296,f656,f87])).

fof(f296,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f295])).

fof(f3290,plain,
    ( spl7_190
    | ~ spl7_36
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f668,f655,f288,f3288])).

fof(f3288,plain,
    ( spl7_190
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK3),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_190])])).

fof(f288,plain,
    ( spl7_36
  <=> v1_relat_1(k5_relat_1(sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f668,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK3),k1_xboole_0))
    | ~ spl7_36
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f289,f656,f87])).

fof(f289,plain,
    ( v1_relat_1(k5_relat_1(sK4,sK3))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f288])).

fof(f3215,plain,
    ( spl7_188
    | ~ spl7_34
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f667,f655,f280,f3213])).

fof(f3213,plain,
    ( spl7_188
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_188])])).

fof(f280,plain,
    ( spl7_34
  <=> v1_relat_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f667,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),k1_xboole_0))
    | ~ spl7_34
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f281,f656,f87])).

fof(f281,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f280])).

fof(f3208,plain,
    ( spl7_186
    | ~ spl7_40
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f662,f655,f302,f3206])).

fof(f3206,plain,
    ( spl7_186
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_186])])).

fof(f662,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK4,sK4)))
    | ~ spl7_40
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f303,f656,f87])).

fof(f3201,plain,
    ( spl7_184
    | ~ spl7_38
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f661,f655,f295,f3199])).

fof(f3199,plain,
    ( spl7_184
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_184])])).

fof(f661,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK4)))
    | ~ spl7_38
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f296,f656,f87])).

fof(f3194,plain,
    ( spl7_182
    | ~ spl7_36
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f660,f655,f288,f3192])).

fof(f3192,plain,
    ( spl7_182
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_182])])).

fof(f660,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK4,sK3)))
    | ~ spl7_36
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f289,f656,f87])).

fof(f3187,plain,
    ( spl7_180
    | ~ spl7_34
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f659,f655,f280,f3185])).

fof(f3185,plain,
    ( spl7_180
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_180])])).

fof(f659,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK3)))
    | ~ spl7_34
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f281,f656,f87])).

fof(f3119,plain,
    ( ~ spl7_179
    | spl7_59 ),
    inference(avatar_split_clause,[],[f493,f477,f3117])).

fof(f3117,plain,
    ( spl7_179
  <=> ~ r2_hidden(sK0,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_179])])).

fof(f493,plain,
    ( ~ r2_hidden(sK0,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl7_59 ),
    inference(unit_resulting_resolution,[],[f82,f478,f105])).

fof(f3112,plain,
    ( ~ spl7_177
    | spl7_51 ),
    inference(avatar_split_clause,[],[f487,f408,f3110])).

fof(f3110,plain,
    ( spl7_177
  <=> ~ r2_hidden(sK1,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_177])])).

fof(f487,plain,
    ( ~ r2_hidden(sK1,sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl7_51 ),
    inference(unit_resulting_resolution,[],[f82,f409,f105])).

fof(f2898,plain,
    ( spl7_174
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f1075,f159,f2896])).

fof(f1075,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f1042,f998])).

fof(f1042,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK0,sK1,sK3,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f160,f160,f108])).

fof(f2640,plain,
    ( spl7_172
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f1074,f166,f159,f2638])).

fof(f1074,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f1043,f999])).

fof(f1043,plain,
    ( m1_subset_1(k4_relset_1(sK1,sK2,sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f160,f108])).

fof(f2368,plain,
    ( spl7_170
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f1071,f166,f159,f2366])).

fof(f1071,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f1046,f1002])).

fof(f1046,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f160,f167,f108])).

fof(f2181,plain,
    ( spl7_168
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f1070,f166,f2179])).

fof(f1070,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f1047,f1003])).

fof(f1047,plain,
    ( m1_subset_1(k4_relset_1(sK1,sK2,sK1,sK2,sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f167,f108])).

fof(f2162,plain,
    ( spl7_166
    | ~ spl7_20
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f375,f302,f208,f2160])).

fof(f2160,plain,
    ( spl7_166
  <=> v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_166])])).

fof(f375,plain,
    ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,sK4)))
    | ~ spl7_20
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f209,f303,f87])).

fof(f2155,plain,
    ( spl7_164
    | ~ spl7_18
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f374,f302,f201,f2153])).

fof(f2153,plain,
    ( spl7_164
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_164])])).

fof(f374,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,sK4)))
    | ~ spl7_18
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f202,f303,f87])).

fof(f2136,plain,
    ( spl7_162
    | ~ spl7_20
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f368,f302,f208,f2134])).

fof(f2134,plain,
    ( spl7_162
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_162])])).

fof(f368,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK4),sK4))
    | ~ spl7_20
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f209,f303,f87])).

fof(f1987,plain,
    ( spl7_160
    | ~ spl7_152 ),
    inference(avatar_split_clause,[],[f1530,f1502,f1985])).

fof(f1765,plain,
    ( spl7_158
    | ~ spl7_156 ),
    inference(avatar_split_clause,[],[f1665,f1644,f1763])).

fof(f1644,plain,
    ( spl7_156
  <=> v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).

fof(f1665,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_156 ),
    inference(unit_resulting_resolution,[],[f1645,f81])).

fof(f1645,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl7_156 ),
    inference(avatar_component_clause,[],[f1644])).

fof(f1646,plain,
    ( spl7_156
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f1639,f142,f1644])).

fof(f1639,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f82,f1638,f86])).

fof(f1638,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f1592,f439])).

fof(f1592,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_relat_1(sK6(X1,k1_xboole_0)))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f143,f605,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',t5_subset)).

fof(f1511,plain,
    ( spl7_154
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f1456,f142,f1509])).

fof(f1509,plain,
    ( spl7_154
  <=> v1_relat_1(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f1456,plain,
    ( v1_relat_1(k1_relat_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f1435,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',cc1_relset_1)).

fof(f1504,plain,
    ( spl7_152
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f1455,f142,f1502])).

fof(f1455,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f143,f1435,f83])).

fof(f1400,plain,
    ( spl7_150
    | ~ spl7_18
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f367,f302,f201,f1398])).

fof(f1398,plain,
    ( spl7_150
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_150])])).

fof(f367,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK4),sK3))
    | ~ spl7_18
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f202,f303,f87])).

fof(f1393,plain,
    ( spl7_148
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f361,f295,f208,f1391])).

fof(f1391,plain,
    ( spl7_148
  <=> v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_148])])).

fof(f361,plain,
    ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,sK4)))
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f209,f296,f87])).

fof(f1386,plain,
    ( spl7_146
    | ~ spl7_18
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f360,f295,f201,f1384])).

fof(f1384,plain,
    ( spl7_146
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f360,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK4)))
    | ~ spl7_18
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f202,f296,f87])).

fof(f1379,plain,
    ( spl7_144
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f355,f295,f208,f1377])).

fof(f1377,plain,
    ( spl7_144
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f355,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),sK4))
    | ~ spl7_20
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f209,f296,f87])).

fof(f1372,plain,
    ( spl7_142
    | ~ spl7_18
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f354,f295,f201,f1370])).

fof(f1370,plain,
    ( spl7_142
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_142])])).

fof(f354,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK4),sK3))
    | ~ spl7_18
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f202,f296,f87])).

fof(f1364,plain,
    ( spl7_140
    | ~ spl7_20
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f349,f288,f208,f1362])).

fof(f1362,plain,
    ( spl7_140
  <=> v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_140])])).

fof(f349,plain,
    ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK4,sK3)))
    | ~ spl7_20
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f209,f289,f87])).

fof(f1357,plain,
    ( spl7_138
    | ~ spl7_18
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f348,f288,f201,f1355])).

fof(f1355,plain,
    ( spl7_138
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f348,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK4,sK3)))
    | ~ spl7_18
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f202,f289,f87])).

fof(f1350,plain,
    ( spl7_136
    | ~ spl7_20
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f344,f288,f208,f1348])).

fof(f1348,plain,
    ( spl7_136
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).

fof(f344,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK3),sK4))
    | ~ spl7_20
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f209,f289,f87])).

fof(f1343,plain,
    ( spl7_134
    | ~ spl7_18
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f343,f288,f201,f1341])).

fof(f1341,plain,
    ( spl7_134
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_134])])).

fof(f343,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK4,sK3),sK3))
    | ~ spl7_18
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f202,f289,f87])).

fof(f1336,plain,
    ( spl7_132
    | ~ spl7_20
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f339,f280,f208,f1334])).

fof(f1334,plain,
    ( spl7_132
  <=> v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_132])])).

fof(f339,plain,
    ( v1_relat_1(k5_relat_1(sK4,k5_relat_1(sK3,sK3)))
    | ~ spl7_20
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f209,f281,f87])).

fof(f1328,plain,
    ( spl7_130
    | ~ spl7_18
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f338,f280,f201,f1326])).

fof(f1326,plain,
    ( spl7_130
  <=> v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_130])])).

fof(f338,plain,
    ( v1_relat_1(k5_relat_1(sK3,k5_relat_1(sK3,sK3)))
    | ~ spl7_18
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f202,f281,f87])).

fof(f1321,plain,
    ( spl7_128
    | ~ spl7_20
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f335,f280,f208,f1319])).

fof(f1319,plain,
    ( spl7_128
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f335,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK4))
    | ~ spl7_20
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f209,f281,f87])).

fof(f1314,plain,
    ( spl7_126
    | ~ spl7_18
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f334,f280,f201,f1312])).

fof(f1312,plain,
    ( spl7_126
  <=> v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f334,plain,
    ( v1_relat_1(k5_relat_1(k5_relat_1(sK3,sK3),sK3))
    | ~ spl7_18
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f202,f281,f87])).

fof(f1301,plain,
    ( spl7_124
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f522,f166,f1299])).

fof(f1299,plain,
    ( spl7_124
  <=> k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_124])])).

fof(f522,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f96])).

fof(f1245,plain,
    ( spl7_122
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f521,f159,f1243])).

fof(f1243,plain,
    ( spl7_122
  <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_122])])).

fof(f521,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f160,f96])).

fof(f1029,plain,
    ( spl7_120
    | ~ spl7_4
    | ~ spl7_12
    | spl7_25 ),
    inference(avatar_split_clause,[],[f939,f222,f166,f132,f1027])).

fof(f939,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f223,f133,f167,f99])).

fof(f1022,plain,
    ( ~ spl7_119
    | ~ spl7_10
    | ~ spl7_12
    | spl7_47 ),
    inference(avatar_split_clause,[],[f1015,f323,f166,f159,f1020])).

fof(f323,plain,
    ( spl7_47
  <=> ~ v1_funct_2(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f1015,plain,
    ( ~ v1_funct_2(k5_relat_1(sK3,sK4),sK0,sK2)
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_47 ),
    inference(backward_demodulation,[],[f1002,f324])).

fof(f324,plain,
    ( ~ v1_funct_2(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),sK0,sK2)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f323])).

fof(f997,plain,
    ( spl7_116
    | ~ spl7_2
    | ~ spl7_10
    | spl7_23 ),
    inference(avatar_split_clause,[],[f850,f219,f159,f125,f995])).

fof(f125,plain,
    ( spl7_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f850,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f220,f126,f160,f99])).

fof(f126,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f987,plain,
    ( spl7_114
    | ~ spl7_98 ),
    inference(avatar_split_clause,[],[f842,f838,f985])).

fof(f985,plain,
    ( spl7_114
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f842,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_98 ),
    inference(superposition,[],[f82,f839])).

fof(f963,plain,
    ( spl7_112
    | ~ spl7_4
    | ~ spl7_12
    | spl7_25
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f943,f581,f222,f166,f132,f961])).

fof(f961,plain,
    ( spl7_112
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f581,plain,
    ( spl7_70
  <=> m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f943,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_25
    | ~ spl7_70 ),
    inference(backward_demodulation,[],[f941,f582])).

fof(f582,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK1))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f581])).

fof(f941,plain,
    ( k1_relat_1(sK4) = sK1
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_25 ),
    inference(backward_demodulation,[],[f939,f497])).

fof(f497,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f95])).

fof(f956,plain,
    ( spl7_110
    | ~ spl7_4
    | ~ spl7_12
    | spl7_25 ),
    inference(avatar_split_clause,[],[f941,f222,f166,f132,f954])).

fof(f933,plain,
    ( spl7_108
    | ~ spl7_2
    | ~ spl7_10
    | spl7_23
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f866,f588,f219,f159,f125,f931])).

fof(f931,plain,
    ( spl7_108
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f588,plain,
    ( spl7_72
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f866,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_23
    | ~ spl7_72 ),
    inference(backward_demodulation,[],[f864,f589])).

fof(f589,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f588])).

fof(f864,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_23 ),
    inference(backward_demodulation,[],[f850,f496])).

fof(f926,plain,
    ( spl7_106
    | ~ spl7_2
    | ~ spl7_10
    | spl7_23 ),
    inference(avatar_split_clause,[],[f864,f219,f159,f125,f924])).

fof(f910,plain,
    ( spl7_104
    | ~ spl7_2
    | ~ spl7_10
    | spl7_23
    | ~ spl7_76 ),
    inference(avatar_split_clause,[],[f865,f614,f219,f159,f125,f908])).

fof(f908,plain,
    ( spl7_104
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f614,plain,
    ( spl7_76
  <=> r1_tarski(k1_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f865,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_23
    | ~ spl7_76 ),
    inference(backward_demodulation,[],[f864,f615])).

fof(f615,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f614])).

fof(f900,plain,
    ( ~ spl7_24
    | spl7_55
    | ~ spl7_98 ),
    inference(avatar_contradiction_clause,[],[f899])).

fof(f899,plain,
    ( $false
    | ~ spl7_24
    | ~ spl7_55
    | ~ spl7_98 ),
    inference(subsumption_resolution,[],[f885,f842])).

fof(f885,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_24
    | ~ spl7_55 ),
    inference(backward_demodulation,[],[f226,f464])).

fof(f898,plain,
    ( ~ spl7_6
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f897])).

fof(f897,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f884,f143])).

fof(f884,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(backward_demodulation,[],[f226,f394])).

fof(f394,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_44 ),
    inference(resolution,[],[f317,f90])).

fof(f317,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl7_44
  <=> r2_hidden(sK5(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f896,plain,
    ( ~ spl7_6
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f895])).

fof(f895,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f881,f154])).

fof(f881,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(backward_demodulation,[],[f226,f317])).

fof(f877,plain,
    ( ~ spl7_30
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f876])).

fof(f876,plain,
    ( $false
    | ~ spl7_30
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f260,f394])).

fof(f260,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl7_30
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f874,plain,
    ( spl7_102
    | ~ spl7_4
    | ~ spl7_12
    | spl7_25
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f862,f596,f222,f166,f132,f872])).

fof(f872,plain,
    ( spl7_102
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f596,plain,
    ( spl7_74
  <=> r1_tarski(k1_relat_1(sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f862,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_25
    | ~ spl7_74 ),
    inference(backward_demodulation,[],[f861,f597])).

fof(f597,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1)
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f596])).

fof(f861,plain,
    ( k1_relat_1(sK4) = sK1
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_25 ),
    inference(backward_demodulation,[],[f851,f497])).

fof(f851,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ spl7_4
    | ~ spl7_12
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f223,f133,f167,f99])).

fof(f849,plain,
    ( spl7_100
    | ~ spl7_98 ),
    inference(avatar_split_clause,[],[f841,f838,f847])).

fof(f847,plain,
    ( spl7_100
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f841,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_98 ),
    inference(superposition,[],[f169,f839])).

fof(f169,plain,(
    ! [X0] : r1_tarski(sK5(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f82,f88])).

fof(f840,plain,
    ( spl7_98
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f547,f530,f838])).

fof(f530,plain,
    ( spl7_68
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f547,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_68 ),
    inference(unit_resulting_resolution,[],[f531,f81])).

fof(f531,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f530])).

fof(f801,plain,
    ( spl7_96
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f666,f655,f799])).

fof(f666,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f656,f656,f87])).

fof(f708,plain,
    ( spl7_94
    | ~ spl7_20
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f672,f655,f208,f706])).

fof(f706,plain,
    ( spl7_94
  <=> v1_relat_1(k5_relat_1(sK4,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f672,plain,
    ( v1_relat_1(k5_relat_1(sK4,k1_xboole_0))
    | ~ spl7_20
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f209,f656,f87])).

fof(f701,plain,
    ( spl7_92
    | ~ spl7_18
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f671,f655,f201,f699])).

fof(f671,plain,
    ( v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl7_18
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f202,f656,f87])).

fof(f694,plain,
    ( spl7_90
    | ~ spl7_20
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f664,f655,f208,f692])).

fof(f664,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK4))
    | ~ spl7_20
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f209,f656,f87])).

fof(f687,plain,
    ( spl7_88
    | ~ spl7_18
    | ~ spl7_86 ),
    inference(avatar_split_clause,[],[f663,f655,f201,f685])).

fof(f663,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | ~ spl7_18
    | ~ spl7_86 ),
    inference(unit_resulting_resolution,[],[f202,f656,f87])).

fof(f657,plain,
    ( spl7_86
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f650,f142,f655])).

fof(f650,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_6 ),
    inference(superposition,[],[f92,f439])).

fof(f646,plain,
    ( spl7_84
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f639,f628,f644])).

fof(f628,plain,
    ( spl7_80
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f639,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl7_80 ),
    inference(unit_resulting_resolution,[],[f629,f88])).

fof(f629,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl7_80 ),
    inference(avatar_component_clause,[],[f628])).

fof(f638,plain,
    ( spl7_82
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f631,f621,f636])).

fof(f636,plain,
    ( spl7_82
  <=> r1_tarski(k2_relat_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f621,plain,
    ( spl7_78
  <=> m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f631,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2)
    | ~ spl7_78 ),
    inference(unit_resulting_resolution,[],[f622,f88])).

fof(f622,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2))
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f621])).

fof(f630,plain,
    ( spl7_80
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f608,f159,f628])).

fof(f608,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f599,f521])).

fof(f599,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f160,f98])).

fof(f623,plain,
    ( spl7_78
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f607,f166,f621])).

fof(f607,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f600,f522])).

fof(f600,plain,
    ( m1_subset_1(k2_relset_1(sK1,sK2,sK4),k1_zfmisc_1(sK2))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f98])).

fof(f616,plain,
    ( spl7_76
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f609,f588,f614])).

fof(f609,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl7_72 ),
    inference(unit_resulting_resolution,[],[f589,f88])).

fof(f598,plain,
    ( spl7_74
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f591,f581,f596])).

fof(f591,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1)
    | ~ spl7_70 ),
    inference(unit_resulting_resolution,[],[f582,f88])).

fof(f590,plain,
    ( spl7_72
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f576,f159,f588])).

fof(f576,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f567,f496])).

fof(f567,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f160,f97])).

fof(f583,plain,
    ( spl7_70
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f575,f166,f581])).

fof(f575,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK1))
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f568,f497])).

fof(f568,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,sK4),k1_zfmisc_1(sK1))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f97])).

fof(f532,plain,
    ( spl7_68
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f525,f142,f530])).

fof(f525,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f82,f283,f86])).

fof(f283,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f143,f82,f106])).

fof(f520,plain,
    ( ~ spl7_67
    | spl7_59 ),
    inference(avatar_split_clause,[],[f494,f477,f518])).

fof(f518,plain,
    ( spl7_67
  <=> ~ r2_hidden(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f494,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_59 ),
    inference(unit_resulting_resolution,[],[f478,f85])).

fof(f513,plain,
    ( ~ spl7_65
    | spl7_55 ),
    inference(avatar_split_clause,[],[f491,f463,f511])).

fof(f491,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_55 ),
    inference(unit_resulting_resolution,[],[f464,f85])).

fof(f506,plain,
    ( ~ spl7_63
    | spl7_51 ),
    inference(avatar_split_clause,[],[f488,f408,f504])).

fof(f504,plain,
    ( spl7_63
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f488,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_51 ),
    inference(unit_resulting_resolution,[],[f409,f85])).

fof(f486,plain,
    ( ~ spl7_61
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f398,f330,f484])).

fof(f484,plain,
    ( spl7_61
  <=> ~ r2_hidden(sK0,sK5(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f330,plain,
    ( spl7_48
  <=> r2_hidden(sK5(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f398,plain,
    ( ~ r2_hidden(sK0,sK5(sK0))
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f331,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',antisymmetry_r2_hidden)).

fof(f331,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f330])).

fof(f479,plain,
    ( ~ spl7_59
    | ~ spl7_6
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f395,f330,f142,f477])).

fof(f395,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f143,f331,f106])).

fof(f472,plain,
    ( ~ spl7_57
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f389,f316,f470])).

fof(f389,plain,
    ( ~ r2_hidden(sK2,sK5(sK2))
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f317,f84])).

fof(f465,plain,
    ( ~ spl7_55
    | ~ spl7_6
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f386,f316,f142,f463])).

fof(f386,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f143,f317,f106])).

fof(f417,plain,
    ( ~ spl7_53
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f380,f309,f415])).

fof(f415,plain,
    ( spl7_53
  <=> ~ r2_hidden(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f309,plain,
    ( spl7_42
  <=> r2_hidden(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f380,plain,
    ( ~ r2_hidden(sK1,sK5(sK1))
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f310,f84])).

fof(f310,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f309])).

fof(f410,plain,
    ( ~ spl7_51
    | ~ spl7_6
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f377,f309,f142,f408])).

fof(f377,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_6
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f143,f310,f106])).

fof(f332,plain,
    ( spl7_48
    | spl7_33 ),
    inference(avatar_split_clause,[],[f274,f269,f330])).

fof(f269,plain,
    ( spl7_33
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f274,plain,
    ( r2_hidden(sK5(sK0),sK0)
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f82,f270,f86])).

fof(f270,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f269])).

fof(f325,plain,(
    ~ spl7_47 ),
    inference(avatar_split_clause,[],[f78,f323])).

fof(f78,plain,(
    ~ v1_funct_2(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),sK0,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ~ v1_funct_2(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),sK0,sK2)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK2
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f37,f66,f65])).

fof(f65,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ v1_funct_2(k4_relset_1(X0,X1,X1,X2,X3,X4),X0,X2)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 = X2
              | k1_xboole_0 != X1 )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1) )
   => ( ? [X4] :
          ( ~ v1_funct_2(k4_relset_1(sK0,sK1,sK1,sK2,sK3,X4),sK0,sK2)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 = sK2
            | k1_xboole_0 != sK1 )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ v1_funct_2(k4_relset_1(X0,X1,X1,X2,X3,X4),X0,X2)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 = X2
            | k1_xboole_0 != X1 )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2) )
     => ( ~ v1_funct_2(k4_relset_1(X0,X1,X1,X2,X3,sK4),X0,X2)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 = X2
          | k1_xboole_0 != X1 )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v1_funct_2(k4_relset_1(X0,X1,X1,X2,X3,X4),X0,X2)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 = X2
            | k1_xboole_0 != X1 )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v1_funct_2(k4_relset_1(X0,X1,X1,X2,X3,X4),X0,X2)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 = X2
            | k1_xboole_0 != X1 )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2) )
           => ( ~ ( k1_xboole_0 != X0
                  & k1_xboole_0 != X2
                  & k1_xboole_0 = X1 )
             => v1_funct_2(k4_relset_1(X0,X1,X1,X2,X3,X4),X0,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2) )
         => ( ~ ( k1_xboole_0 != X0
                & k1_xboole_0 != X2
                & k1_xboole_0 = X1 )
           => v1_funct_2(k4_relset_1(X0,X1,X1,X2,X3,X4),X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',t19_funct_2)).

fof(f318,plain,
    ( spl7_44
    | spl7_31 ),
    inference(avatar_split_clause,[],[f272,f262,f316])).

fof(f262,plain,
    ( spl7_31
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f272,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f82,f263,f86])).

fof(f263,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f262])).

fof(f311,plain,
    ( spl7_42
    | spl7_29 ),
    inference(avatar_split_clause,[],[f250,f247,f309])).

fof(f247,plain,
    ( spl7_29
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f250,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f82,f248,f86])).

fof(f248,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f247])).

fof(f304,plain,
    ( spl7_40
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f239,f208,f302])).

fof(f239,plain,
    ( v1_relat_1(k5_relat_1(sK4,sK4))
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f209,f209,f87])).

fof(f297,plain,
    ( spl7_38
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f238,f208,f201,f295])).

fof(f238,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f202,f209,f87])).

fof(f290,plain,
    ( spl7_36
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f235,f208,f201,f288])).

fof(f235,plain,
    ( v1_relat_1(k5_relat_1(sK4,sK3))
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f202,f209,f87])).

fof(f282,plain,
    ( spl7_34
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f214,f201,f280])).

fof(f214,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f202,f202,f87])).

fof(f271,plain,
    ( ~ spl7_33
    | ~ spl7_6
    | spl7_27 ),
    inference(avatar_split_clause,[],[f257,f228,f142,f269])).

fof(f257,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl7_6
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f143,f229,f89])).

fof(f264,plain,
    ( ~ spl7_31
    | ~ spl7_6
    | spl7_25 ),
    inference(avatar_split_clause,[],[f254,f222,f142,f262])).

fof(f254,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_6
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f143,f223,f89])).

fof(f249,plain,
    ( ~ spl7_29
    | ~ spl7_6
    | spl7_23 ),
    inference(avatar_split_clause,[],[f242,f219,f142,f247])).

fof(f242,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_6
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f143,f220,f89])).

fof(f233,plain,
    ( ~ spl7_23
    | spl7_24
    | spl7_26 ),
    inference(avatar_split_clause,[],[f77,f231,f225,f219])).

fof(f77,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f67])).

fof(f210,plain,
    ( spl7_20
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f194,f166,f208])).

fof(f194,plain,
    ( v1_relat_1(sK4)
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f94])).

fof(f203,plain,
    ( spl7_18
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f193,f159,f201])).

fof(f193,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f160,f94])).

fof(f185,plain,
    ( spl7_16
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f171,f166,f183])).

fof(f183,plain,
    ( spl7_16
  <=> r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f171,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f167,f88])).

fof(f178,plain,
    ( spl7_14
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f170,f159,f176])).

fof(f176,plain,
    ( spl7_14
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f170,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f160,f88])).

fof(f168,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f76,f166])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f67])).

fof(f161,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f74,f159])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f153,plain,
    ( spl7_8
    | ~ spl7_0 ),
    inference(avatar_split_clause,[],[f135,f118,f151])).

fof(f151,plain,
    ( spl7_8
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f118,plain,
    ( spl7_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f135,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl7_0 ),
    inference(unit_resulting_resolution,[],[f119,f81])).

fof(f119,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f118])).

fof(f144,plain,
    ( spl7_6
    | ~ spl7_0 ),
    inference(avatar_split_clause,[],[f137,f118,f142])).

fof(f137,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_0 ),
    inference(backward_demodulation,[],[f135,f119])).

fof(f134,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f75,f132])).

fof(f75,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f127,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f73,f125])).

fof(f73,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f120,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f79,f118])).

fof(f79,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t19_funct_2.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
