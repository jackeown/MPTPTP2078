%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t24_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:08 EDT 2019

% Result     : Theorem 1.07s
% Output     : Refutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :  636 (1972 expanded)
%              Number of leaves         :  147 ( 796 expanded)
%              Depth                    :   14
%              Number of atoms          : 1839 (5007 expanded)
%              Number of equality atoms :  127 ( 654 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4819,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f111,f124,f145,f152,f159,f169,f179,f189,f213,f220,f227,f235,f248,f255,f263,f276,f283,f297,f304,f327,f372,f408,f415,f417,f421,f433,f440,f447,f460,f467,f474,f487,f494,f528,f535,f542,f549,f556,f571,f589,f596,f603,f626,f635,f642,f649,f656,f663,f672,f679,f694,f701,f714,f746,f814,f876,f916,f998,f1056,f1216,f1266,f1488,f1672,f1950,f1954,f2042,f2134,f2527,f2779,f2830,f2840,f2842,f2845,f2848,f2849,f2855,f2857,f2861,f2887,f2897,f2899,f2901,f2904,f2907,f2908,f3052,f3066,f3073,f3095,f3102,f3115,f3128,f3150,f3297,f3306,f3313,f3320,f3321,f3328,f3335,f3356,f3369,f3386,f3393,f3400,f3441,f3448,f3495,f3539,f3617,f3621,f3972,f4202,f4521,f4540,f4694,f4752,f4754,f4774,f4790,f4797,f4808,f4810,f4818])).

fof(f4818,plain,
    ( ~ spl13_6
    | spl13_79
    | ~ spl13_82
    | ~ spl13_88 ),
    inference(avatar_contradiction_clause,[],[f4817])).

fof(f4817,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_79
    | ~ spl13_82
    | ~ spl13_88 ),
    inference(subsumption_resolution,[],[f4816,f531])).

fof(f531,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_79 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl13_79
  <=> ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_79])])).

fof(f4816,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_82
    | ~ spl13_88 ),
    inference(subsumption_resolution,[],[f4815,f548])).

fof(f548,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl13_82 ),
    inference(avatar_component_clause,[],[f547])).

fof(f547,plain,
    ( spl13_82
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_82])])).

fof(f4815,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_88 ),
    inference(subsumption_resolution,[],[f4813,f123])).

fof(f123,plain,
    ( v1_relat_1(sK2)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl13_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f4813,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_88 ),
    inference(resolution,[],[f585,f1133])).

fof(f1133,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k1_relat_1(k4_relat_1(X6)))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(k4_relat_1(X6))
      | r2_hidden(X7,k2_relat_1(X6)) ) ),
    inference(resolution,[],[f350,f89])).

fof(f89,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',d5_relat_1)).

fof(f350,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK4(k4_relat_1(X2),X3),X3),X2)
      | ~ v1_relat_1(k4_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(k4_relat_1(X2))) ) ),
    inference(resolution,[],[f90,f86])).

fof(f86,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',d4_relat_1)).

fof(f90,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | r2_hidden(k4_tarski(X3,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X3,X2),X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k4_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',d7_relat_1)).

fof(f585,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_88 ),
    inference(avatar_component_clause,[],[f584])).

fof(f584,plain,
    ( spl13_88
  <=> r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_88])])).

fof(f4810,plain,
    ( ~ spl13_76
    | spl13_99 ),
    inference(avatar_contradiction_clause,[],[f4809])).

fof(f4809,plain,
    ( $false
    | ~ spl13_76
    | ~ spl13_99 ),
    inference(subsumption_resolution,[],[f4806,f641])).

fof(f641,plain,
    ( ~ m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_99 ),
    inference(avatar_component_clause,[],[f640])).

fof(f640,plain,
    ( spl13_99
  <=> ~ m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_99])])).

fof(f4806,plain,
    ( m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_76 ),
    inference(resolution,[],[f524,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',t1_subset)).

fof(f524,plain,
    ( r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_76 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl13_76
  <=> r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_76])])).

fof(f4808,plain,
    ( ~ spl13_44
    | ~ spl13_76
    | spl13_139 ),
    inference(avatar_contradiction_clause,[],[f4807])).

fof(f4807,plain,
    ( $false
    | ~ spl13_44
    | ~ spl13_76
    | ~ spl13_139 ),
    inference(subsumption_resolution,[],[f4805,f1484])).

fof(f1484,plain,
    ( ~ m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),sK1)
    | ~ spl13_139 ),
    inference(avatar_component_clause,[],[f1483])).

fof(f1483,plain,
    ( spl13_139
  <=> ~ m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_139])])).

fof(f4805,plain,
    ( m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),sK1)
    | ~ spl13_44
    | ~ spl13_76 ),
    inference(resolution,[],[f524,f345])).

fof(f345,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | m1_subset_1(X0,sK1) )
    | ~ spl13_44 ),
    inference(resolution,[],[f326,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',t4_subset)).

fof(f326,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl13_44 ),
    inference(avatar_component_clause,[],[f325])).

fof(f325,plain,
    ( spl13_44
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_44])])).

fof(f4797,plain,
    ( ~ spl13_6
    | spl13_77
    | ~ spl13_82
    | ~ spl13_86 ),
    inference(avatar_contradiction_clause,[],[f4796])).

fof(f4796,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_77
    | ~ spl13_82
    | ~ spl13_86 ),
    inference(subsumption_resolution,[],[f4795,f527])).

fof(f527,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_77 ),
    inference(avatar_component_clause,[],[f526])).

fof(f526,plain,
    ( spl13_77
  <=> ~ r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_77])])).

fof(f4795,plain,
    ( r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_82
    | ~ spl13_86 ),
    inference(subsumption_resolution,[],[f4794,f548])).

fof(f4794,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_86 ),
    inference(subsumption_resolution,[],[f4792,f123])).

fof(f4792,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_86 ),
    inference(resolution,[],[f570,f1133])).

fof(f570,plain,
    ( r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_86 ),
    inference(avatar_component_clause,[],[f569])).

fof(f569,plain,
    ( spl13_86
  <=> r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_86])])).

fof(f4790,plain,
    ( ~ spl13_73
    | spl13_119
    | ~ spl13_148 ),
    inference(avatar_split_clause,[],[f4779,f2037,f709,f482])).

fof(f482,plain,
    ( spl13_73
  <=> ~ v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_73])])).

fof(f709,plain,
    ( spl13_119
  <=> ~ v1_xboole_0(k2_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_119])])).

fof(f2037,plain,
    ( spl13_148
  <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_148])])).

fof(f4779,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl13_119
    | ~ spl13_148 ),
    inference(forward_demodulation,[],[f710,f2038])).

fof(f2038,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl13_148 ),
    inference(avatar_component_clause,[],[f2037])).

fof(f710,plain,
    ( ~ v1_xboole_0(k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_119 ),
    inference(avatar_component_clause,[],[f709])).

fof(f4774,plain,
    ( ~ spl13_72
    | ~ spl13_112
    | spl13_183 ),
    inference(avatar_contradiction_clause,[],[f4773])).

fof(f4773,plain,
    ( $false
    | ~ spl13_72
    | ~ spl13_112
    | ~ spl13_183 ),
    inference(subsumption_resolution,[],[f4771,f3365])).

fof(f3365,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ spl13_183 ),
    inference(avatar_component_clause,[],[f3364])).

fof(f3364,plain,
    ( spl13_183
  <=> k1_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_183])])).

fof(f4771,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl13_72
    | ~ spl13_112 ),
    inference(resolution,[],[f693,f2862])).

fof(f2862,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_relat_1(sK2) = X0 )
    | ~ spl13_72 ),
    inference(resolution,[],[f486,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',t8_boole)).

fof(f486,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl13_72 ),
    inference(avatar_component_clause,[],[f485])).

fof(f485,plain,
    ( spl13_72
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f693,plain,
    ( v1_xboole_0(k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_112 ),
    inference(avatar_component_clause,[],[f692])).

fof(f692,plain,
    ( spl13_112
  <=> v1_xboole_0(k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_112])])).

fof(f4754,plain,
    ( ~ spl13_6
    | ~ spl13_10
    | ~ spl13_82
    | spl13_163
    | spl13_165
    | spl13_173
    | ~ spl13_176 ),
    inference(avatar_contradiction_clause,[],[f4753])).

fof(f4753,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_82
    | ~ spl13_163
    | ~ spl13_165
    | ~ spl13_173
    | ~ spl13_176 ),
    inference(subsumption_resolution,[],[f4748,f3327])).

fof(f3327,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_176 ),
    inference(avatar_component_clause,[],[f3326])).

fof(f3326,plain,
    ( spl13_176
  <=> r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_176])])).

fof(f4748,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_82
    | ~ spl13_163
    | ~ spl13_165
    | ~ spl13_173 ),
    inference(resolution,[],[f3204,f3312])).

fof(f3312,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_173 ),
    inference(avatar_component_clause,[],[f3311])).

fof(f3311,plain,
    ( spl13_173
  <=> ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_173])])).

fof(f3204,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_82
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f2833])).

fof(f2833,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK2))) )
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_82 ),
    inference(subsumption_resolution,[],[f2832,f123])).

fof(f2832,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK2))) )
    | ~ spl13_10
    | ~ spl13_82 ),
    inference(forward_demodulation,[],[f2831,f151])).

fof(f151,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = sK2
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl13_10
  <=> k4_relat_1(k4_relat_1(sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f2831,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_relat_1(k4_relat_1(k4_relat_1(sK2)))
        | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK2))) )
    | ~ spl13_10
    | ~ spl13_82 ),
    inference(subsumption_resolution,[],[f2825,f548])).

fof(f2825,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_relat_1(k4_relat_1(sK2))
        | ~ v1_relat_1(k4_relat_1(k4_relat_1(sK2)))
        | ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK2))) )
    | ~ spl13_10 ),
    inference(superposition,[],[f947,f151])).

fof(f947,plain,(
    ! [X8,X9] :
      ( r2_hidden(X9,k2_relat_1(k4_relat_1(X8)))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(k4_relat_1(X8))
      | ~ r2_hidden(X9,k1_relat_1(X8)) ) ),
    inference(resolution,[],[f357,f86])).

fof(f357,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X10,X11),X9)
      | ~ v1_relat_1(k4_relat_1(X9))
      | ~ v1_relat_1(X9)
      | r2_hidden(X10,k2_relat_1(k4_relat_1(X9))) ) ),
    inference(resolution,[],[f91,f89])).

fof(f91,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X3,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k4_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3126,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(subsumption_resolution,[],[f3121,f3114])).

fof(f3114,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_165 ),
    inference(avatar_component_clause,[],[f3113])).

fof(f3113,plain,
    ( spl13_165
  <=> ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_165])])).

fof(f3121,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2))
    | k1_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl13_163 ),
    inference(resolution,[],[f3108,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | r2_hidden(sK9(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',t2_tarski)).

fof(f3108,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_163 ),
    inference(avatar_component_clause,[],[f3107])).

fof(f3107,plain,
    ( spl13_163
  <=> ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_163])])).

fof(f4752,plain,
    ( ~ spl13_6
    | ~ spl13_10
    | ~ spl13_82
    | spl13_163
    | spl13_165
    | spl13_171
    | ~ spl13_174 ),
    inference(avatar_contradiction_clause,[],[f4751])).

fof(f4751,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_82
    | ~ spl13_163
    | ~ spl13_165
    | ~ spl13_171
    | ~ spl13_174 ),
    inference(subsumption_resolution,[],[f4747,f3319])).

fof(f3319,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_174 ),
    inference(avatar_component_clause,[],[f3318])).

fof(f3318,plain,
    ( spl13_174
  <=> r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_174])])).

fof(f4747,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_82
    | ~ spl13_163
    | ~ spl13_165
    | ~ spl13_171 ),
    inference(resolution,[],[f3204,f3305])).

fof(f3305,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_171 ),
    inference(avatar_component_clause,[],[f3304])).

fof(f3304,plain,
    ( spl13_171
  <=> ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_171])])).

fof(f4694,plain,
    ( spl13_156
    | ~ spl13_130
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3159,f3113,f3107,f996,f3047])).

fof(f3047,plain,
    ( spl13_156
  <=> k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_156])])).

fof(f996,plain,
    ( spl13_130
  <=> k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_130])])).

fof(f3159,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(sK2)
    | ~ spl13_130
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f997])).

fof(f997,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl13_130 ),
    inference(avatar_component_clause,[],[f996])).

fof(f4540,plain,
    ( spl13_204
    | ~ spl13_66
    | ~ spl13_88
    | ~ spl13_130
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3207,f3113,f3107,f996,f584,f465,f4538])).

fof(f4538,plain,
    ( spl13_204
  <=> m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_204])])).

fof(f465,plain,
    ( spl13_66
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f3207,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),sK1)
    | ~ spl13_66
    | ~ spl13_88
    | ~ spl13_130
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f3099])).

fof(f3099,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),sK1)
    | ~ spl13_66
    | ~ spl13_88
    | ~ spl13_130 ),
    inference(resolution,[],[f585,f1161])).

fof(f1161,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK2)))
        | m1_subset_1(X0,sK1) )
    | ~ spl13_66
    | ~ spl13_130 ),
    inference(subsumption_resolution,[],[f1158,f466])).

fof(f466,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl13_66 ),
    inference(avatar_component_clause,[],[f465])).

fof(f1158,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k4_relat_1(sK2)))
        | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | m1_subset_1(X0,sK1) )
    | ~ spl13_130 ),
    inference(superposition,[],[f319,f997])).

fof(f319,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ r2_hidden(X19,k1_relset_1(X17,X18,X16))
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | m1_subset_1(X19,X17) ) ),
    inference(resolution,[],[f78,f81])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',dt_k1_relset_1)).

fof(f4521,plain,
    ( spl13_202
    | ~ spl13_138
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3185,f3113,f3107,f1486,f4519])).

fof(f4519,plain,
    ( spl13_202
  <=> m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_202])])).

fof(f1486,plain,
    ( spl13_138
  <=> m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_138])])).

fof(f3185,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),sK1)
    | ~ spl13_138
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f1487])).

fof(f1487,plain,
    ( m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),sK1)
    | ~ spl13_138 ),
    inference(avatar_component_clause,[],[f1486])).

fof(f4202,plain,
    ( spl13_200
    | ~ spl13_128
    | ~ spl13_148 ),
    inference(avatar_split_clause,[],[f3633,f2037,f914,f4200])).

fof(f4200,plain,
    ( spl13_200
  <=> m1_subset_1(sK9(k1_relat_1(sK2),k1_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_200])])).

fof(f914,plain,
    ( spl13_128
  <=> m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_128])])).

fof(f3633,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),k1_relat_1(sK2)),sK0)
    | ~ spl13_128
    | ~ spl13_148 ),
    inference(backward_demodulation,[],[f2038,f915])).

fof(f915,plain,
    ( m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),sK0)
    | ~ spl13_128 ),
    inference(avatar_component_clause,[],[f914])).

fof(f3972,plain,
    ( spl13_198
    | ~ spl13_44
    | ~ spl13_66
    | ~ spl13_130
    | spl13_163
    | spl13_165
    | spl13_169
    | ~ spl13_182 ),
    inference(avatar_split_clause,[],[f3532,f3367,f3295,f3113,f3107,f996,f465,f325,f3970])).

fof(f3970,plain,
    ( spl13_198
  <=> m1_subset_1(sK3(k4_relat_1(sK2),k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_198])])).

fof(f3295,plain,
    ( spl13_169
  <=> k1_relat_1(sK2) != k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_169])])).

fof(f3367,plain,
    ( spl13_182
  <=> k1_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_182])])).

fof(f3532,plain,
    ( m1_subset_1(sK3(k4_relat_1(sK2),k2_relat_1(sK2)),sK1)
    | ~ spl13_44
    | ~ spl13_66
    | ~ spl13_130
    | ~ spl13_163
    | ~ spl13_165
    | ~ spl13_169
    | ~ spl13_182 ),
    inference(subsumption_resolution,[],[f3531,f3160])).

fof(f3160,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | m1_subset_1(X0,sK1) )
    | ~ spl13_66
    | ~ spl13_130
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f1161])).

fof(f3531,plain,
    ( r2_hidden(sK3(k4_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2))
    | m1_subset_1(sK3(k4_relat_1(sK2),k2_relat_1(sK2)),sK1)
    | ~ spl13_44
    | ~ spl13_169
    | ~ spl13_182 ),
    inference(subsumption_resolution,[],[f3523,f3296])).

fof(f3296,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK2)
    | ~ spl13_169 ),
    inference(avatar_component_clause,[],[f3295])).

fof(f3523,plain,
    ( r2_hidden(sK3(k4_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2))
    | k1_relat_1(sK2) = k2_relat_1(sK2)
    | m1_subset_1(sK3(k4_relat_1(sK2),k2_relat_1(sK2)),sK1)
    | ~ spl13_44
    | ~ spl13_182 ),
    inference(resolution,[],[f3378,f345])).

fof(f3378,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(k4_relat_1(sK2),X3),k1_relat_1(sK2))
        | r2_hidden(sK3(k4_relat_1(sK2),X3),X3)
        | k1_relat_1(sK2) = X3 )
    | ~ spl13_182 ),
    inference(forward_demodulation,[],[f3373,f3368])).

fof(f3368,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl13_182 ),
    inference(avatar_component_clause,[],[f3367])).

fof(f3373,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(k4_relat_1(sK2),X3),k1_relat_1(sK2))
        | r2_hidden(sK3(k4_relat_1(sK2),X3),X3)
        | k1_relat_1(k4_relat_1(sK2)) = X3 )
    | ~ spl13_182 ),
    inference(superposition,[],[f375,f3368])).

fof(f375,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK3(X4,X5),k1_relat_1(X4))
      | r2_hidden(sK3(X4,X5),X5)
      | k1_relat_1(X4) = X5 ) ),
    inference(resolution,[],[f64,f87])).

fof(f87,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f3621,plain,
    ( ~ spl13_6
    | spl13_81
    | ~ spl13_82
    | ~ spl13_90 ),
    inference(avatar_contradiction_clause,[],[f3620])).

fof(f3620,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_81
    | ~ spl13_82
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f3619,f538])).

fof(f538,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_81 ),
    inference(avatar_component_clause,[],[f537])).

fof(f537,plain,
    ( spl13_81
  <=> ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_81])])).

fof(f3619,plain,
    ( r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_82
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f3618,f548])).

fof(f3618,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_90 ),
    inference(subsumption_resolution,[],[f3577,f123])).

fof(f3577,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_90 ),
    inference(resolution,[],[f1107,f592])).

fof(f592,plain,
    ( r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_90 ),
    inference(avatar_component_clause,[],[f591])).

fof(f591,plain,
    ( spl13_90
  <=> r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).

fof(f1107,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k2_relat_1(k4_relat_1(X8)))
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(k4_relat_1(X8))
      | r2_hidden(X9,k1_relat_1(X8)) ) ),
    inference(resolution,[],[f349,f87])).

fof(f349,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,sK7(k4_relat_1(X0),X1)),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(k4_relat_1(X0))) ) ),
    inference(resolution,[],[f90,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f3617,plain,
    ( ~ spl13_6
    | ~ spl13_82
    | spl13_85
    | ~ spl13_92 ),
    inference(avatar_contradiction_clause,[],[f3616])).

fof(f3616,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_82
    | ~ spl13_85
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f3615,f555])).

fof(f555,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_85 ),
    inference(avatar_component_clause,[],[f554])).

fof(f554,plain,
    ( spl13_85
  <=> ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_85])])).

fof(f3615,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_82
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f3614,f548])).

fof(f3614,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f3576,f123])).

fof(f3576,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_92 ),
    inference(resolution,[],[f1107,f602])).

fof(f602,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_92 ),
    inference(avatar_component_clause,[],[f601])).

fof(f601,plain,
    ( spl13_92
  <=> r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k2_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f3539,plain,
    ( spl13_196
    | ~ spl13_52
    | ~ spl13_176 ),
    inference(avatar_split_clause,[],[f3348,f3326,f413,f3537])).

fof(f3537,plain,
    ( spl13_196
  <=> m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_196])])).

fof(f413,plain,
    ( spl13_52
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_52])])).

fof(f3348,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),sK0)
    | ~ spl13_52
    | ~ spl13_176 ),
    inference(resolution,[],[f3327,f418])).

fof(f418,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | m1_subset_1(X0,sK0) )
    | ~ spl13_52 ),
    inference(resolution,[],[f414,f81])).

fof(f414,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl13_52 ),
    inference(avatar_component_clause,[],[f413])).

fof(f3495,plain,
    ( spl13_194
    | ~ spl13_52
    | ~ spl13_174 ),
    inference(avatar_split_clause,[],[f3345,f3318,f413,f3493])).

fof(f3493,plain,
    ( spl13_194
  <=> m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_194])])).

fof(f3345,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),sK0)
    | ~ spl13_52
    | ~ spl13_174 ),
    inference(resolution,[],[f3319,f418])).

fof(f3448,plain,
    ( ~ spl13_193
    | spl13_163
    | spl13_165
    | spl13_167 ),
    inference(avatar_split_clause,[],[f3209,f3145,f3113,f3107,f3446])).

fof(f3446,plain,
    ( spl13_193
  <=> ~ m1_subset_1(sK9(k1_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_193])])).

fof(f3145,plain,
    ( spl13_167
  <=> ~ m1_subset_1(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_167])])).

fof(f3209,plain,
    ( ~ m1_subset_1(sK9(k1_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_163
    | ~ spl13_165
    | ~ spl13_167 ),
    inference(backward_demodulation,[],[f3126,f3146])).

fof(f3146,plain,
    ( ~ m1_subset_1(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_167 ),
    inference(avatar_component_clause,[],[f3145])).

fof(f3441,plain,
    ( spl13_190
    | ~ spl13_110
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3158,f3113,f3107,f683,f3439])).

fof(f3439,plain,
    ( spl13_190
  <=> m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_190])])).

fof(f683,plain,
    ( spl13_110
  <=> m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_110])])).

fof(f3158,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_110
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f684])).

fof(f684,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_110 ),
    inference(avatar_component_clause,[],[f683])).

fof(f3400,plain,
    ( spl13_188
    | ~ spl13_106
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3157,f3113,f3107,f670,f3398])).

fof(f3398,plain,
    ( spl13_188
  <=> m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_188])])).

fof(f670,plain,
    ( spl13_106
  <=> m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_106])])).

fof(f3157,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_106
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f671])).

fof(f671,plain,
    ( m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_106 ),
    inference(avatar_component_clause,[],[f670])).

fof(f3393,plain,
    ( ~ spl13_187
    | spl13_99
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3156,f3113,f3107,f640,f3391])).

fof(f3391,plain,
    ( spl13_187
  <=> ~ m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_187])])).

fof(f3156,plain,
    ( ~ m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_99
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f641])).

fof(f3386,plain,
    ( ~ spl13_185
    | spl13_97
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3155,f3113,f3107,f630,f3384])).

fof(f3384,plain,
    ( spl13_185
  <=> ~ m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_185])])).

fof(f630,plain,
    ( spl13_97
  <=> ~ m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_97])])).

fof(f3155,plain,
    ( ~ m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_97
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f631])).

fof(f631,plain,
    ( ~ m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_97 ),
    inference(avatar_component_clause,[],[f630])).

fof(f3369,plain,
    ( spl13_182
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3126,f3113,f3107,f3367])).

fof(f3356,plain,
    ( spl13_180
    | ~ spl13_140
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3189,f3113,f3107,f1670,f3354])).

fof(f3354,plain,
    ( spl13_180
  <=> m1_subset_1(sK12(k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_180])])).

fof(f1670,plain,
    ( spl13_140
  <=> m1_subset_1(sK12(k1_relat_1(k4_relat_1(sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_140])])).

fof(f3189,plain,
    ( m1_subset_1(sK12(k1_relat_1(sK2)),sK1)
    | ~ spl13_140
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f1671])).

fof(f1671,plain,
    ( m1_subset_1(sK12(k1_relat_1(k4_relat_1(sK2))),sK1)
    | ~ spl13_140 ),
    inference(avatar_component_clause,[],[f1670])).

fof(f3335,plain,
    ( ~ spl13_179
    | spl13_159
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3206,f3113,f3107,f3064,f3333])).

fof(f3333,plain,
    ( spl13_179
  <=> ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_179])])).

fof(f3064,plain,
    ( spl13_159
  <=> ~ r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_159])])).

fof(f3206,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_159
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f3065])).

fof(f3065,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_159 ),
    inference(avatar_component_clause,[],[f3064])).

fof(f3328,plain,
    ( spl13_176
    | ~ spl13_88
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3154,f3113,f3107,f584,f3326])).

fof(f3154,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_88
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f585])).

fof(f3321,plain,
    ( spl13_160
    | ~ spl13_136
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3162,f3113,f3107,f1264,f3071])).

fof(f3071,plain,
    ( spl13_160
  <=> m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_160])])).

fof(f1264,plain,
    ( spl13_136
  <=> m1_subset_1(k1_relat_1(k4_relat_1(sK2)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_136])])).

fof(f3162,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl13_136
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f1265])).

fof(f1265,plain,
    ( m1_subset_1(k1_relat_1(k4_relat_1(sK2)),k1_zfmisc_1(sK1))
    | ~ spl13_136 ),
    inference(avatar_component_clause,[],[f1264])).

fof(f3320,plain,
    ( spl13_174
    | ~ spl13_86
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3153,f3113,f3107,f569,f3318])).

fof(f3153,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_86
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f570])).

fof(f3313,plain,
    ( ~ spl13_173
    | spl13_79
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3152,f3113,f3107,f530,f3311])).

fof(f3152,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_79
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f531])).

fof(f3306,plain,
    ( ~ spl13_171
    | spl13_77
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3151,f3113,f3107,f526,f3304])).

fof(f3151,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_77
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3126,f527])).

fof(f3297,plain,
    ( ~ spl13_169
    | spl13_15
    | ~ spl13_130
    | spl13_163
    | spl13_165 ),
    inference(avatar_split_clause,[],[f3210,f3113,f3107,f996,f167,f3295])).

fof(f167,plain,
    ( spl13_15
  <=> k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f3210,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK2)
    | ~ spl13_15
    | ~ spl13_130
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(backward_demodulation,[],[f3159,f168])).

fof(f168,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relat_1(sK2)
    | ~ spl13_15 ),
    inference(avatar_component_clause,[],[f167])).

fof(f3150,plain,
    ( spl13_166
    | ~ spl13_162 ),
    inference(avatar_split_clause,[],[f3132,f3104,f3148])).

fof(f3148,plain,
    ( spl13_166
  <=> m1_subset_1(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_166])])).

fof(f3104,plain,
    ( spl13_162
  <=> r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_162])])).

fof(f3132,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_162 ),
    inference(resolution,[],[f3105,f84])).

fof(f3105,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_162 ),
    inference(avatar_component_clause,[],[f3104])).

fof(f3128,plain,
    ( ~ spl13_130
    | spl13_157
    | spl13_163
    | spl13_165 ),
    inference(avatar_contradiction_clause,[],[f3127])).

fof(f3127,plain,
    ( $false
    | ~ spl13_130
    | ~ spl13_157
    | ~ spl13_163
    | ~ spl13_165 ),
    inference(subsumption_resolution,[],[f3126,f3055])).

fof(f3055,plain,
    ( k1_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ spl13_130
    | ~ spl13_157 ),
    inference(superposition,[],[f3051,f997])).

fof(f3051,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k1_relat_1(sK2)
    | ~ spl13_157 ),
    inference(avatar_component_clause,[],[f3050])).

fof(f3050,plain,
    ( spl13_157
  <=> k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_157])])).

fof(f3115,plain,
    ( ~ spl13_163
    | ~ spl13_165
    | ~ spl13_130
    | spl13_157 ),
    inference(avatar_split_clause,[],[f3074,f3050,f996,f3113,f3107])).

fof(f3074,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_130
    | ~ spl13_157 ),
    inference(forward_demodulation,[],[f3057,f997])).

fof(f3057,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_130
    | ~ spl13_157 ),
    inference(forward_demodulation,[],[f3054,f997])).

fof(f3054,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ r2_hidden(sK9(k1_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_157 ),
    inference(extensionality_resolution,[],[f71,f3051])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | ~ r2_hidden(sK9(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3102,plain,
    ( ~ spl13_66
    | ~ spl13_88
    | spl13_127
    | ~ spl13_130 ),
    inference(avatar_contradiction_clause,[],[f3101])).

fof(f3101,plain,
    ( $false
    | ~ spl13_66
    | ~ spl13_88
    | ~ spl13_127
    | ~ spl13_130 ),
    inference(subsumption_resolution,[],[f3099,f872])).

fof(f872,plain,
    ( ~ m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),sK1)
    | ~ spl13_127 ),
    inference(avatar_component_clause,[],[f871])).

fof(f871,plain,
    ( spl13_127
  <=> ~ m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_127])])).

fof(f3095,plain,
    ( spl13_88
    | ~ spl13_32
    | ~ spl13_130 ),
    inference(avatar_split_clause,[],[f2902,f996,f243,f584])).

fof(f243,plain,
    ( spl13_32
  <=> r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relset_1(sK1,sK0,k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f2902,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_32
    | ~ spl13_130 ),
    inference(forward_demodulation,[],[f244,f997])).

fof(f244,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_32 ),
    inference(avatar_component_clause,[],[f243])).

fof(f3073,plain,
    ( spl13_160
    | ~ spl13_44
    | ~ spl13_64
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f2916,f485,f458,f325,f3071])).

fof(f458,plain,
    ( spl13_64
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_64])])).

fof(f2916,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl13_44
    | ~ spl13_64
    | ~ spl13_72 ),
    inference(backward_demodulation,[],[f2912,f326])).

fof(f2912,plain,
    ( k1_relat_1(sK2) = k2_relat_1(sK2)
    | ~ spl13_64
    | ~ spl13_72 ),
    inference(resolution,[],[f459,f2862])).

fof(f459,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl13_64 ),
    inference(avatar_component_clause,[],[f458])).

fof(f3066,plain,
    ( ~ spl13_159
    | ~ spl13_64
    | ~ spl13_72
    | spl13_77 ),
    inference(avatar_split_clause,[],[f2919,f526,f485,f458,f3064])).

fof(f2919,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_64
    | ~ spl13_72
    | ~ spl13_77 ),
    inference(backward_demodulation,[],[f2912,f527])).

fof(f3052,plain,
    ( ~ spl13_157
    | spl13_15
    | ~ spl13_64
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f2914,f485,f458,f167,f3050])).

fof(f2914,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k1_relat_1(sK2)
    | ~ spl13_15
    | ~ spl13_64
    | ~ spl13_72 ),
    inference(backward_demodulation,[],[f2912,f168])).

fof(f2908,plain,
    ( ~ spl13_79
    | spl13_31
    | ~ spl13_130 ),
    inference(avatar_split_clause,[],[f2905,f996,f240,f530])).

fof(f240,plain,
    ( spl13_31
  <=> ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_31])])).

fof(f2905,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_31
    | ~ spl13_130 ),
    inference(forward_demodulation,[],[f241,f997])).

fof(f241,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_31 ),
    inference(avatar_component_clause,[],[f240])).

fof(f2907,plain,
    ( spl13_31
    | spl13_111
    | ~ spl13_130
    | spl13_135 ),
    inference(avatar_contradiction_clause,[],[f2906])).

fof(f2906,plain,
    ( $false
    | ~ spl13_31
    | ~ spl13_111
    | ~ spl13_130
    | ~ spl13_135 ),
    inference(subsumption_resolution,[],[f2905,f2894])).

fof(f2894,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_111
    | ~ spl13_135 ),
    inference(subsumption_resolution,[],[f800,f1215])).

fof(f1215,plain,
    ( k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(sK2)
    | ~ spl13_135 ),
    inference(avatar_component_clause,[],[f1214])).

fof(f1214,plain,
    ( spl13_135
  <=> k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_135])])).

fof(f800,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2)
    | ~ spl13_111 ),
    inference(resolution,[],[f190,f687])).

fof(f687,plain,
    ( ~ m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_111 ),
    inference(avatar_component_clause,[],[f686])).

fof(f686,plain,
    ( spl13_111
  <=> ~ m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_111])])).

fof(f190,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | m1_subset_1(sK9(X0,X1),X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f70,f84])).

fof(f2904,plain,
    ( ~ spl13_32
    | spl13_111
    | ~ spl13_130
    | spl13_135 ),
    inference(avatar_contradiction_clause,[],[f2903])).

fof(f2903,plain,
    ( $false
    | ~ spl13_32
    | ~ spl13_111
    | ~ spl13_130
    | ~ spl13_135 ),
    inference(subsumption_resolution,[],[f2902,f2895])).

fof(f2895,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_111
    | ~ spl13_135 ),
    inference(subsumption_resolution,[],[f1328,f2894])).

fof(f1328,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_135 ),
    inference(extensionality_resolution,[],[f71,f1215])).

fof(f2901,plain,
    ( spl13_79
    | spl13_111
    | spl13_135 ),
    inference(avatar_contradiction_clause,[],[f2900])).

fof(f2900,plain,
    ( $false
    | ~ spl13_79
    | ~ spl13_111
    | ~ spl13_135 ),
    inference(subsumption_resolution,[],[f531,f2894])).

fof(f2899,plain,
    ( ~ spl13_88
    | spl13_111
    | spl13_135 ),
    inference(avatar_contradiction_clause,[],[f2898])).

fof(f2898,plain,
    ( $false
    | ~ spl13_88
    | ~ spl13_111
    | ~ spl13_135 ),
    inference(subsumption_resolution,[],[f585,f2895])).

fof(f2897,plain,
    ( ~ spl13_44
    | spl13_65
    | ~ spl13_96
    | spl13_127 ),
    inference(avatar_contradiction_clause,[],[f2896])).

fof(f2896,plain,
    ( $false
    | ~ spl13_44
    | ~ spl13_65
    | ~ spl13_96
    | ~ spl13_127 ),
    inference(subsumption_resolution,[],[f872,f680])).

fof(f680,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),sK1)
    | ~ spl13_44
    | ~ spl13_65
    | ~ spl13_96 ),
    inference(resolution,[],[f582,f634])).

fof(f634,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_96 ),
    inference(avatar_component_clause,[],[f633])).

fof(f633,plain,
    ( spl13_96
  <=> m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_96])])).

fof(f582,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k2_relat_1(sK2))
        | m1_subset_1(X5,sK1) )
    | ~ spl13_44
    | ~ spl13_65 ),
    inference(subsumption_resolution,[],[f578,f456])).

fof(f456,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ spl13_65 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl13_65
  <=> ~ v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_65])])).

fof(f578,plain,
    ( ! [X5] :
        ( m1_subset_1(X5,sK1)
        | v1_xboole_0(k2_relat_1(sK2))
        | ~ m1_subset_1(X5,k2_relat_1(sK2)) )
    | ~ spl13_44 ),
    inference(resolution,[],[f345,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',t2_subset)).

fof(f2887,plain,
    ( ~ spl13_6
    | ~ spl13_78
    | ~ spl13_82
    | spl13_89 ),
    inference(avatar_contradiction_clause,[],[f2886])).

fof(f2886,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_78
    | ~ spl13_82
    | ~ spl13_89 ),
    inference(subsumption_resolution,[],[f2885,f534])).

fof(f534,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_78 ),
    inference(avatar_component_clause,[],[f533])).

fof(f533,plain,
    ( spl13_78
  <=> r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_78])])).

fof(f2885,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_82
    | ~ spl13_89 ),
    inference(subsumption_resolution,[],[f2884,f548])).

fof(f2884,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_89 ),
    inference(subsumption_resolution,[],[f2879,f123])).

fof(f2879,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_89 ),
    inference(resolution,[],[f955,f588])).

fof(f588,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_89 ),
    inference(avatar_component_clause,[],[f587])).

fof(f587,plain,
    ( spl13_89
  <=> ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_89])])).

fof(f955,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,k1_relat_1(k4_relat_1(X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k4_relat_1(X2))
      | ~ r2_hidden(X3,k2_relat_1(X2)) ) ),
    inference(resolution,[],[f358,f88])).

fof(f358,plain,(
    ! [X14,X12,X13] :
      ( ~ r2_hidden(k4_tarski(X13,X14),X12)
      | ~ v1_relat_1(k4_relat_1(X12))
      | ~ v1_relat_1(X12)
      | r2_hidden(X14,k1_relat_1(k4_relat_1(X12))) ) ),
    inference(resolution,[],[f91,f87])).

fof(f2861,plain,
    ( spl13_72
    | spl13_81
    | ~ spl13_102 ),
    inference(avatar_split_clause,[],[f2856,f654,f537,f485])).

fof(f654,plain,
    ( spl13_102
  <=> m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_102])])).

fof(f2856,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl13_81
    | ~ spl13_102 ),
    inference(subsumption_resolution,[],[f2852,f655])).

fof(f655,plain,
    ( m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_102 ),
    inference(avatar_component_clause,[],[f654])).

fof(f2852,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_81 ),
    inference(resolution,[],[f538,f83])).

fof(f2857,plain,
    ( spl13_90
    | ~ spl13_36
    | ~ spl13_132 ),
    inference(avatar_split_clause,[],[f2846,f1054,f265,f591])).

fof(f265,plain,
    ( spl13_36
  <=> r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relset_1(sK1,sK0,k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f1054,plain,
    ( spl13_132
  <=> k2_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_132])])).

fof(f2846,plain,
    ( r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_36
    | ~ spl13_132 ),
    inference(forward_demodulation,[],[f266,f1055])).

fof(f1055,plain,
    ( k2_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl13_132 ),
    inference(avatar_component_clause,[],[f1054])).

fof(f266,plain,
    ( r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_36 ),
    inference(avatar_component_clause,[],[f265])).

fof(f2855,plain,
    ( spl13_73
    | spl13_81
    | ~ spl13_102 ),
    inference(avatar_contradiction_clause,[],[f2854])).

fof(f2854,plain,
    ( $false
    | ~ spl13_73
    | ~ spl13_81
    | ~ spl13_102 ),
    inference(subsumption_resolution,[],[f2853,f655])).

fof(f2853,plain,
    ( ~ m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_73
    | ~ spl13_81 ),
    inference(subsumption_resolution,[],[f2852,f483])).

fof(f483,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl13_73 ),
    inference(avatar_component_clause,[],[f482])).

fof(f2849,plain,
    ( ~ spl13_81
    | spl13_39
    | ~ spl13_132 ),
    inference(avatar_split_clause,[],[f2843,f1054,f274,f537])).

fof(f274,plain,
    ( spl13_39
  <=> ~ r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_39])])).

fof(f2843,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_39
    | ~ spl13_132 ),
    inference(forward_demodulation,[],[f275,f1055])).

fof(f275,plain,
    ( ~ r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_39 ),
    inference(avatar_component_clause,[],[f274])).

fof(f2848,plain,
    ( ~ spl13_36
    | spl13_117
    | ~ spl13_132
    | spl13_149 ),
    inference(avatar_contradiction_clause,[],[f2847])).

fof(f2847,plain,
    ( $false
    | ~ spl13_36
    | ~ spl13_117
    | ~ spl13_132
    | ~ spl13_149 ),
    inference(subsumption_resolution,[],[f2846,f2838])).

fof(f2838,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_117
    | ~ spl13_149 ),
    inference(subsumption_resolution,[],[f2142,f2837])).

fof(f2837,plain,
    ( r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_117
    | ~ spl13_149 ),
    inference(subsumption_resolution,[],[f834,f2041])).

fof(f2041,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | ~ spl13_149 ),
    inference(avatar_component_clause,[],[f2040])).

fof(f2040,plain,
    ( spl13_149
  <=> k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_149])])).

fof(f834,plain,
    ( r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl13_117 ),
    inference(resolution,[],[f191,f707])).

fof(f707,plain,
    ( ~ m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_117 ),
    inference(avatar_component_clause,[],[f706])).

fof(f706,plain,
    ( spl13_117
  <=> ~ m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_117])])).

fof(f191,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | m1_subset_1(sK9(X0,X1),X0)
      | X0 = X1 ) ),
    inference(resolution,[],[f70,f84])).

fof(f2142,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_149 ),
    inference(extensionality_resolution,[],[f71,f2041])).

fof(f2845,plain,
    ( spl13_39
    | spl13_117
    | ~ spl13_132
    | spl13_149 ),
    inference(avatar_contradiction_clause,[],[f2844])).

fof(f2844,plain,
    ( $false
    | ~ spl13_39
    | ~ spl13_117
    | ~ spl13_132
    | ~ spl13_149 ),
    inference(subsumption_resolution,[],[f2843,f2837])).

fof(f2842,plain,
    ( spl13_81
    | spl13_117
    | spl13_149 ),
    inference(avatar_contradiction_clause,[],[f2841])).

fof(f2841,plain,
    ( $false
    | ~ spl13_81
    | ~ spl13_117
    | ~ spl13_149 ),
    inference(subsumption_resolution,[],[f538,f2837])).

fof(f2840,plain,
    ( ~ spl13_90
    | spl13_117
    | spl13_149 ),
    inference(avatar_contradiction_clause,[],[f2839])).

fof(f2839,plain,
    ( $false
    | ~ spl13_90
    | ~ spl13_117
    | ~ spl13_149 ),
    inference(subsumption_resolution,[],[f592,f2838])).

fof(f2830,plain,
    ( ~ spl13_6
    | ~ spl13_80
    | ~ spl13_82
    | spl13_91 ),
    inference(avatar_contradiction_clause,[],[f2829])).

fof(f2829,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_80
    | ~ spl13_82
    | ~ spl13_91 ),
    inference(subsumption_resolution,[],[f2828,f541])).

fof(f541,plain,
    ( r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_80 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl13_80
  <=> r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_80])])).

fof(f2828,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_82
    | ~ spl13_91 ),
    inference(subsumption_resolution,[],[f2827,f548])).

fof(f2827,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_6
    | ~ spl13_91 ),
    inference(subsumption_resolution,[],[f2822,f123])).

fof(f2822,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_91 ),
    inference(resolution,[],[f947,f595])).

fof(f595,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_91 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl13_91
  <=> ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_91])])).

fof(f2779,plain,
    ( spl13_154
    | ~ spl13_66
    | spl13_119
    | ~ spl13_132 ),
    inference(avatar_split_clause,[],[f2705,f1054,f709,f465,f2777])).

fof(f2777,plain,
    ( spl13_154
  <=> m1_subset_1(sK12(k2_relat_1(k4_relat_1(sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_154])])).

fof(f2705,plain,
    ( m1_subset_1(sK12(k2_relat_1(k4_relat_1(sK2))),sK0)
    | ~ spl13_66
    | ~ spl13_119
    | ~ spl13_132 ),
    inference(resolution,[],[f2357,f85])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK12(X0),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',existence_m1_subset_1)).

fof(f2357,plain,
    ( ! [X17] :
        ( ~ m1_subset_1(X17,k2_relat_1(k4_relat_1(sK2)))
        | m1_subset_1(X17,sK0) )
    | ~ spl13_66
    | ~ spl13_119
    | ~ spl13_132 ),
    inference(subsumption_resolution,[],[f2342,f710])).

fof(f2342,plain,
    ( ! [X17] :
        ( m1_subset_1(X17,sK0)
        | v1_xboole_0(k2_relat_1(k4_relat_1(sK2)))
        | ~ m1_subset_1(X17,k2_relat_1(k4_relat_1(sK2))) )
    | ~ spl13_66
    | ~ spl13_132 ),
    inference(resolution,[],[f1969,f83])).

fof(f1969,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k4_relat_1(sK2)))
        | m1_subset_1(X0,sK0) )
    | ~ spl13_66
    | ~ spl13_132 ),
    inference(subsumption_resolution,[],[f1966,f466])).

fof(f1966,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k4_relat_1(sK2)))
        | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | m1_subset_1(X0,sK0) )
    | ~ spl13_132 ),
    inference(superposition,[],[f311,f1055])).

fof(f311,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ r2_hidden(X19,k2_relset_1(X17,X18,X16))
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | m1_subset_1(X19,X18) ) ),
    inference(resolution,[],[f77,f81])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',dt_k2_relset_1)).

fof(f2527,plain,
    ( spl13_152
    | ~ spl13_66
    | ~ spl13_92
    | ~ spl13_132 ),
    inference(avatar_split_clause,[],[f2327,f1054,f601,f465,f2525])).

fof(f2525,plain,
    ( spl13_152
  <=> m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_152])])).

fof(f2327,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),sK0)
    | ~ spl13_66
    | ~ spl13_92
    | ~ spl13_132 ),
    inference(resolution,[],[f1969,f602])).

fof(f2134,plain,
    ( spl13_150
    | ~ spl13_66
    | ~ spl13_132 ),
    inference(avatar_split_clause,[],[f1970,f1054,f465,f2132])).

fof(f2132,plain,
    ( spl13_150
  <=> m1_subset_1(k2_relat_1(k4_relat_1(sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_150])])).

fof(f1970,plain,
    ( m1_subset_1(k2_relat_1(k4_relat_1(sK2)),k1_zfmisc_1(sK0))
    | ~ spl13_66
    | ~ spl13_132 ),
    inference(subsumption_resolution,[],[f1968,f466])).

fof(f1968,plain,
    ( m1_subset_1(k2_relat_1(k4_relat_1(sK2)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl13_132 ),
    inference(superposition,[],[f77,f1055])).

fof(f2042,plain,
    ( ~ spl13_149
    | spl13_21
    | ~ spl13_132 ),
    inference(avatar_split_clause,[],[f1965,f1054,f187,f2040])).

fof(f187,plain,
    ( spl13_21
  <=> k2_relset_1(sK1,sK0,k4_relat_1(sK2)) != k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f1965,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | ~ spl13_21
    | ~ spl13_132 ),
    inference(superposition,[],[f188,f1055])).

fof(f188,plain,
    ( k2_relset_1(sK1,sK0,k4_relat_1(sK2)) != k1_relat_1(sK2)
    | ~ spl13_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f1954,plain,
    ( ~ spl13_143
    | spl13_146
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f1079,f406,f1952,f1942])).

fof(f1942,plain,
    ( spl13_143
  <=> ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_143])])).

fof(f1952,plain,
    ( spl13_146
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | m1_subset_1(X1,k2_zfmisc_1(sK1,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_146])])).

fof(f406,plain,
    ( spl13_50
  <=> k3_relset_1(sK0,sK1,k4_relat_1(sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f1079,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | m1_subset_1(X1,k2_zfmisc_1(sK1,sK0)) )
    | ~ spl13_50 ),
    inference(superposition,[],[f339,f407])).

fof(f407,plain,
    ( k3_relset_1(sK0,sK1,k4_relat_1(sK2)) = sK2
    | ~ spl13_50 ),
    inference(avatar_component_clause,[],[f406])).

fof(f339,plain,(
    ! [X17,X15,X18,X16] :
      ( ~ r2_hidden(X18,k3_relset_1(X16,X17,X15))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | m1_subset_1(X18,k2_zfmisc_1(X17,X16)) ) ),
    inference(resolution,[],[f79,f81])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',dt_k3_relset_1)).

fof(f1950,plain,
    ( ~ spl13_143
    | spl13_144
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f416,f406,f1948,f1942])).

fof(f1948,plain,
    ( spl13_144
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_144])])).

fof(f416,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl13_50 ),
    inference(superposition,[],[f79,f407])).

fof(f1672,plain,
    ( spl13_140
    | ~ spl13_66
    | spl13_113
    | ~ spl13_130 ),
    inference(avatar_split_clause,[],[f1607,f996,f689,f465,f1670])).

fof(f689,plain,
    ( spl13_113
  <=> ~ v1_xboole_0(k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_113])])).

fof(f1607,plain,
    ( m1_subset_1(sK12(k1_relat_1(k4_relat_1(sK2))),sK1)
    | ~ spl13_66
    | ~ spl13_113
    | ~ spl13_130 ),
    inference(resolution,[],[f1448,f85])).

fof(f1448,plain,
    ( ! [X12] :
        ( ~ m1_subset_1(X12,k1_relat_1(k4_relat_1(sK2)))
        | m1_subset_1(X12,sK1) )
    | ~ spl13_66
    | ~ spl13_113
    | ~ spl13_130 ),
    inference(subsumption_resolution,[],[f1436,f690])).

fof(f690,plain,
    ( ~ v1_xboole_0(k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_113 ),
    inference(avatar_component_clause,[],[f689])).

fof(f1436,plain,
    ( ! [X12] :
        ( m1_subset_1(X12,sK1)
        | v1_xboole_0(k1_relat_1(k4_relat_1(sK2)))
        | ~ m1_subset_1(X12,k1_relat_1(k4_relat_1(sK2))) )
    | ~ spl13_66
    | ~ spl13_130 ),
    inference(resolution,[],[f1161,f83])).

fof(f1488,plain,
    ( spl13_138
    | ~ spl13_66
    | ~ spl13_86
    | ~ spl13_130 ),
    inference(avatar_split_clause,[],[f1426,f996,f569,f465,f1486])).

fof(f1426,plain,
    ( m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),sK1)
    | ~ spl13_66
    | ~ spl13_86
    | ~ spl13_130 ),
    inference(resolution,[],[f1161,f570])).

fof(f1266,plain,
    ( spl13_136
    | ~ spl13_66
    | ~ spl13_130 ),
    inference(avatar_split_clause,[],[f1162,f996,f465,f1264])).

fof(f1162,plain,
    ( m1_subset_1(k1_relat_1(k4_relat_1(sK2)),k1_zfmisc_1(sK1))
    | ~ spl13_66
    | ~ spl13_130 ),
    inference(subsumption_resolution,[],[f1160,f466])).

fof(f1160,plain,
    ( m1_subset_1(k1_relat_1(k4_relat_1(sK2)),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl13_130 ),
    inference(superposition,[],[f78,f997])).

fof(f1216,plain,
    ( ~ spl13_135
    | spl13_15
    | ~ spl13_130 ),
    inference(avatar_split_clause,[],[f1157,f996,f167,f1214])).

fof(f1157,plain,
    ( k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(sK2)
    | ~ spl13_15
    | ~ spl13_130 ),
    inference(superposition,[],[f168,f997])).

fof(f1056,plain,
    ( spl13_132
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f497,f465,f1054])).

fof(f497,plain,
    ( k2_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl13_66 ),
    inference(resolution,[],[f466,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',redefinition_k2_relset_1)).

fof(f998,plain,
    ( spl13_130
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f496,f465,f996])).

fof(f496,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl13_66 ),
    inference(resolution,[],[f466,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',redefinition_k1_relset_1)).

fof(f916,plain,
    ( spl13_128
    | ~ spl13_52
    | ~ spl13_80 ),
    inference(avatar_split_clause,[],[f604,f540,f413,f914])).

fof(f604,plain,
    ( m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),sK0)
    | ~ spl13_52
    | ~ spl13_80 ),
    inference(resolution,[],[f418,f541])).

fof(f876,plain,
    ( spl13_126
    | ~ spl13_44
    | ~ spl13_78 ),
    inference(avatar_split_clause,[],[f572,f533,f325,f874])).

fof(f874,plain,
    ( spl13_126
  <=> m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_126])])).

fof(f572,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),sK1)
    | ~ spl13_44
    | ~ spl13_78 ),
    inference(resolution,[],[f345,f534])).

fof(f814,plain,
    ( ~ spl13_123
    | spl13_124
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f501,f465,f812,f809])).

fof(f809,plain,
    ( spl13_123
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_123])])).

fof(f812,plain,
    ( spl13_124
  <=> ! [X1] : ~ r2_hidden(X1,k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_124])])).

fof(f501,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k4_relat_1(sK2))
        | ~ v1_xboole_0(k2_zfmisc_1(sK1,sK0)) )
    | ~ spl13_66 ),
    inference(resolution,[],[f466,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',t5_subset)).

fof(f746,plain,
    ( spl13_120
    | ~ spl13_52
    | spl13_73 ),
    inference(avatar_split_clause,[],[f726,f482,f413,f744])).

fof(f744,plain,
    ( spl13_120
  <=> m1_subset_1(sK12(k1_relat_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_120])])).

fof(f726,plain,
    ( m1_subset_1(sK12(k1_relat_1(sK2)),sK0)
    | ~ spl13_52
    | ~ spl13_73 ),
    inference(resolution,[],[f614,f85])).

fof(f614,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_relat_1(sK2))
        | m1_subset_1(X5,sK0) )
    | ~ spl13_52
    | ~ spl13_73 ),
    inference(subsumption_resolution,[],[f610,f483])).

fof(f610,plain,
    ( ! [X5] :
        ( m1_subset_1(X5,sK0)
        | v1_xboole_0(k1_relat_1(sK2))
        | ~ m1_subset_1(X5,k1_relat_1(sK2)) )
    | ~ spl13_52 ),
    inference(resolution,[],[f418,f83])).

fof(f714,plain,
    ( ~ spl13_117
    | spl13_118
    | spl13_37
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f519,f465,f268,f712,f706])).

fof(f712,plain,
    ( spl13_118
  <=> v1_xboole_0(k2_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_118])])).

fof(f268,plain,
    ( spl13_37
  <=> ~ r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relset_1(sK1,sK0,k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_37])])).

fof(f519,plain,
    ( v1_xboole_0(k2_relat_1(k4_relat_1(sK2)))
    | ~ m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_37
    | ~ spl13_66 ),
    inference(forward_demodulation,[],[f513,f497])).

fof(f513,plain,
    ( ~ m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | v1_xboole_0(k2_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_37
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f497,f279])).

fof(f279,plain,
    ( v1_xboole_0(k2_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ m1_subset_1(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_37 ),
    inference(resolution,[],[f269,f83])).

fof(f269,plain,
    ( ~ r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_37 ),
    inference(avatar_component_clause,[],[f268])).

fof(f701,plain,
    ( spl13_114
    | ~ spl13_44
    | spl13_65 ),
    inference(avatar_split_clause,[],[f681,f455,f325,f699])).

fof(f699,plain,
    ( spl13_114
  <=> m1_subset_1(sK12(k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_114])])).

fof(f681,plain,
    ( m1_subset_1(sK12(k2_relat_1(sK2)),sK1)
    | ~ spl13_44
    | ~ spl13_65 ),
    inference(resolution,[],[f582,f85])).

fof(f694,plain,
    ( ~ spl13_111
    | spl13_112
    | spl13_33
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f510,f465,f246,f692,f686])).

fof(f246,plain,
    ( spl13_33
  <=> ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relset_1(sK1,sK0,k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f510,plain,
    ( v1_xboole_0(k1_relat_1(k4_relat_1(sK2)))
    | ~ m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_33
    | ~ spl13_66 ),
    inference(forward_demodulation,[],[f506,f496])).

fof(f506,plain,
    ( ~ m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | v1_xboole_0(k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_33
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f496,f252])).

fof(f252,plain,
    ( v1_xboole_0(k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ m1_subset_1(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_33 ),
    inference(resolution,[],[f247,f83])).

fof(f247,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f246])).

fof(f679,plain,
    ( spl13_108
    | ~ spl13_66
    | ~ spl13_74 ),
    inference(avatar_split_clause,[],[f518,f492,f465,f677])).

fof(f677,plain,
    ( spl13_108
  <=> m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k2_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_108])])).

fof(f492,plain,
    ( spl13_74
  <=> m1_subset_1(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relset_1(sK1,sK0,k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_74])])).

fof(f518,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_66
    | ~ spl13_74 ),
    inference(backward_demodulation,[],[f497,f493])).

fof(f493,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_74 ),
    inference(avatar_component_clause,[],[f492])).

fof(f672,plain,
    ( spl13_106
    | ~ spl13_66
    | ~ spl13_68 ),
    inference(avatar_split_clause,[],[f509,f472,f465,f670])).

fof(f472,plain,
    ( spl13_68
  <=> m1_subset_1(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relset_1(sK1,sK0,k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_68])])).

fof(f509,plain,
    ( m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_66
    | ~ spl13_68 ),
    inference(backward_demodulation,[],[f496,f473])).

fof(f473,plain,
    ( m1_subset_1(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_68 ),
    inference(avatar_component_clause,[],[f472])).

fof(f663,plain,
    ( ~ spl13_105
    | ~ spl13_66
    | spl13_71 ),
    inference(avatar_split_clause,[],[f517,f479,f465,f661])).

fof(f661,plain,
    ( spl13_105
  <=> ~ m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_105])])).

fof(f479,plain,
    ( spl13_71
  <=> ~ m1_subset_1(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_71])])).

fof(f517,plain,
    ( ~ m1_subset_1(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_66
    | ~ spl13_71 ),
    inference(backward_demodulation,[],[f497,f480])).

fof(f480,plain,
    ( ~ m1_subset_1(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_71 ),
    inference(avatar_component_clause,[],[f479])).

fof(f656,plain,
    ( spl13_102
    | ~ spl13_60
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f516,f465,f445,f654])).

fof(f445,plain,
    ( spl13_60
  <=> m1_subset_1(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_60])])).

fof(f516,plain,
    ( m1_subset_1(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_60
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f497,f446])).

fof(f446,plain,
    ( m1_subset_1(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_60 ),
    inference(avatar_component_clause,[],[f445])).

fof(f649,plain,
    ( spl13_100
    | ~ spl13_10
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f521,f465,f150,f647])).

fof(f647,plain,
    ( spl13_100
  <=> k3_relset_1(sK1,sK0,sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_100])])).

fof(f521,plain,
    ( k3_relset_1(sK1,sK0,sK2) = k4_relat_1(sK2)
    | ~ spl13_10
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f520,f495])).

fof(f495,plain,
    ( k3_relset_1(sK1,sK0,k3_relset_1(sK1,sK0,k4_relat_1(sK2))) = k4_relat_1(sK2)
    | ~ spl13_66 ),
    inference(resolution,[],[f466,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,k3_relset_1(X0,X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',involutiveness_k3_relset_1)).

fof(f520,plain,
    ( k3_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK2
    | ~ spl13_10
    | ~ spl13_66 ),
    inference(forward_demodulation,[],[f498,f151])).

fof(f498,plain,
    ( k3_relset_1(sK1,sK0,k4_relat_1(sK2)) = k4_relat_1(k4_relat_1(sK2))
    | ~ spl13_66 ),
    inference(resolution,[],[f466,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',redefinition_k3_relset_1)).

fof(f642,plain,
    ( ~ spl13_99
    | spl13_63
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f508,f465,f452,f640])).

fof(f452,plain,
    ( spl13_63
  <=> ~ m1_subset_1(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_63])])).

fof(f508,plain,
    ( ~ m1_subset_1(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_63
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f496,f453])).

fof(f453,plain,
    ( ~ m1_subset_1(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_63 ),
    inference(avatar_component_clause,[],[f452])).

fof(f635,plain,
    ( spl13_96
    | ~ spl13_58
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f507,f465,f438,f633])).

fof(f438,plain,
    ( spl13_58
  <=> m1_subset_1(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f507,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_58
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f496,f439])).

fof(f439,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_58 ),
    inference(avatar_component_clause,[],[f438])).

fof(f626,plain,
    ( spl13_94
    | ~ spl13_10
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f520,f465,f150,f624])).

fof(f624,plain,
    ( spl13_94
  <=> k3_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_94])])).

fof(f603,plain,
    ( spl13_92
    | ~ spl13_42
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f515,f465,f292,f601])).

fof(f292,plain,
    ( spl13_42
  <=> r2_hidden(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relset_1(sK1,sK0,k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).

fof(f515,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_42
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f497,f293])).

fof(f293,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_42 ),
    inference(avatar_component_clause,[],[f292])).

fof(f596,plain,
    ( ~ spl13_91
    | spl13_37
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f511,f465,f268,f594])).

fof(f511,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl13_37
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f497,f269])).

fof(f589,plain,
    ( ~ spl13_89
    | spl13_33
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f505,f465,f246,f587])).

fof(f505,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_33
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f496,f247])).

fof(f571,plain,
    ( spl13_86
    | ~ spl13_22
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f502,f465,f202,f569])).

fof(f202,plain,
    ( spl13_22
  <=> r2_hidden(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relset_1(sK1,sK0,k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f502,plain,
    ( r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relat_1(k4_relat_1(sK2)))
    | ~ spl13_22
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f496,f203])).

fof(f203,plain,
    ( r2_hidden(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f202])).

fof(f556,plain,
    ( ~ spl13_85
    | spl13_41
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f514,f465,f289,f554])).

fof(f289,plain,
    ( spl13_41
  <=> ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).

fof(f514,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_41
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f497,f290])).

fof(f290,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_41 ),
    inference(avatar_component_clause,[],[f289])).

fof(f549,plain,
    ( spl13_82
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f499,f465,f547])).

fof(f499,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl13_66 ),
    inference(resolution,[],[f466,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',cc1_relset_1)).

fof(f542,plain,
    ( spl13_80
    | ~ spl13_38
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f512,f465,f271,f540])).

fof(f271,plain,
    ( spl13_38
  <=> r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_38])])).

fof(f512,plain,
    ( r2_hidden(sK9(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_38
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f497,f272])).

fof(f272,plain,
    ( r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_38 ),
    inference(avatar_component_clause,[],[f271])).

fof(f535,plain,
    ( spl13_78
    | ~ spl13_30
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f504,f465,f237,f533])).

fof(f237,plain,
    ( spl13_30
  <=> r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f504,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_30
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f496,f238])).

fof(f238,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f237])).

fof(f528,plain,
    ( ~ spl13_77
    | spl13_25
    | ~ spl13_66 ),
    inference(avatar_split_clause,[],[f503,f465,f211,f526])).

fof(f211,plain,
    ( spl13_25
  <=> ~ r2_hidden(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f503,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_25
    | ~ spl13_66 ),
    inference(backward_demodulation,[],[f496,f212])).

fof(f212,plain,
    ( ~ r2_hidden(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_25 ),
    inference(avatar_component_clause,[],[f211])).

fof(f494,plain,
    ( spl13_74
    | ~ spl13_42 ),
    inference(avatar_split_clause,[],[f306,f292,f492])).

fof(f306,plain,
    ( m1_subset_1(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_42 ),
    inference(resolution,[],[f293,f84])).

fof(f487,plain,
    ( ~ spl13_71
    | spl13_72
    | spl13_41 ),
    inference(avatar_split_clause,[],[f298,f289,f485,f479])).

fof(f298,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ m1_subset_1(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_41 ),
    inference(resolution,[],[f290,f83])).

fof(f474,plain,
    ( spl13_68
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f228,f202,f472])).

fof(f228,plain,
    ( m1_subset_1(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_22 ),
    inference(resolution,[],[f203,f84])).

fof(f467,plain,
    ( spl13_66
    | ~ spl13_0
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f342,f218,f96,f465])).

fof(f96,plain,
    ( spl13_0
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f218,plain,
    ( spl13_26
  <=> k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f342,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl13_0
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f341,f97])).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f96])).

fof(f341,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl13_26 ),
    inference(superposition,[],[f79,f219])).

fof(f219,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f218])).

fof(f460,plain,
    ( ~ spl13_63
    | spl13_64
    | spl13_25 ),
    inference(avatar_split_clause,[],[f222,f211,f458,f452])).

fof(f222,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ m1_subset_1(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl13_25 ),
    inference(resolution,[],[f212,f83])).

fof(f447,plain,
    ( spl13_60
    | ~ spl13_38 ),
    inference(avatar_split_clause,[],[f423,f271,f445])).

fof(f423,plain,
    ( m1_subset_1(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_38 ),
    inference(resolution,[],[f272,f84])).

fof(f440,plain,
    ( spl13_58
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f420,f237,f438])).

fof(f420,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_30 ),
    inference(resolution,[],[f238,f84])).

fof(f433,plain,
    ( ~ spl13_55
    | spl13_56
    | ~ spl13_52 ),
    inference(avatar_split_clause,[],[f419,f413,f431,f428])).

fof(f428,plain,
    ( spl13_55
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_55])])).

fof(f431,plain,
    ( spl13_56
  <=> ! [X1] : ~ r2_hidden(X1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f419,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ v1_xboole_0(sK0) )
    | ~ spl13_52 ),
    inference(resolution,[],[f414,f80])).

fof(f421,plain,
    ( spl13_38
    | spl13_21
    | spl13_37 ),
    inference(avatar_split_clause,[],[f284,f268,f187,f271])).

fof(f284,plain,
    ( r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl13_21
    | ~ spl13_37 ),
    inference(subsumption_resolution,[],[f280,f188])).

fof(f280,plain,
    ( r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | k2_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(sK2)
    | ~ spl13_37 ),
    inference(resolution,[],[f269,f70])).

fof(f417,plain,
    ( spl13_30
    | spl13_15
    | spl13_33 ),
    inference(avatar_split_clause,[],[f256,f246,f167,f237])).

fof(f256,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_15
    | ~ spl13_33 ),
    inference(subsumption_resolution,[],[f251,f168])).

fof(f251,plain,
    ( r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relat_1(sK2))
    | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(sK2)
    | ~ spl13_33 ),
    inference(resolution,[],[f247,f70])).

fof(f415,plain,
    ( spl13_52
    | ~ spl13_0
    | ~ spl13_34 ),
    inference(avatar_split_clause,[],[f401,f261,f96,f413])).

fof(f261,plain,
    ( spl13_34
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f401,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl13_0
    | ~ spl13_34 ),
    inference(subsumption_resolution,[],[f400,f97])).

fof(f400,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl13_34 ),
    inference(superposition,[],[f78,f262])).

fof(f262,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f261])).

fof(f408,plain,
    ( spl13_50
    | ~ spl13_0
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f332,f218,f96,f406])).

fof(f332,plain,
    ( k3_relset_1(sK0,sK1,k4_relat_1(sK2)) = sK2
    | ~ spl13_0
    | ~ spl13_26 ),
    inference(forward_demodulation,[],[f330,f219])).

fof(f330,plain,
    ( k3_relset_1(sK0,sK1,k3_relset_1(sK0,sK1,sK2)) = sK2
    | ~ spl13_0 ),
    inference(resolution,[],[f57,f97])).

fof(f372,plain,
    ( ~ spl13_47
    | spl13_48
    | ~ spl13_44 ),
    inference(avatar_split_clause,[],[f346,f325,f370,f367])).

fof(f367,plain,
    ( spl13_47
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_47])])).

fof(f370,plain,
    ( spl13_48
  <=> ! [X1] : ~ r2_hidden(X1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).

fof(f346,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK2))
        | ~ v1_xboole_0(sK1) )
    | ~ spl13_44 ),
    inference(resolution,[],[f326,f80])).

fof(f327,plain,
    ( spl13_44
    | ~ spl13_0
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f314,f233,f96,f325])).

fof(f233,plain,
    ( spl13_28
  <=> k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f314,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl13_0
    | ~ spl13_28 ),
    inference(subsumption_resolution,[],[f313,f97])).

fof(f313,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl13_28 ),
    inference(superposition,[],[f77,f234])).

fof(f234,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f233])).

fof(f304,plain,
    ( spl13_21
    | spl13_41
    | spl13_43 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl13_21
    | ~ spl13_41
    | ~ spl13_43 ),
    inference(subsumption_resolution,[],[f302,f188])).

fof(f302,plain,
    ( k2_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(sK2)
    | ~ spl13_41
    | ~ spl13_43 ),
    inference(subsumption_resolution,[],[f300,f290])).

fof(f300,plain,
    ( r2_hidden(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relat_1(sK2))
    | k2_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(sK2)
    | ~ spl13_43 ),
    inference(resolution,[],[f296,f70])).

fof(f296,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_43 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl13_43
  <=> ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relset_1(sK1,sK0,k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_43])])).

fof(f297,plain,
    ( ~ spl13_41
    | ~ spl13_43
    | spl13_21 ),
    inference(avatar_split_clause,[],[f196,f187,f295,f289])).

fof(f196,plain,
    ( ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ r2_hidden(sK9(k1_relat_1(sK2),k2_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_21 ),
    inference(extensionality_resolution,[],[f71,f188])).

fof(f283,plain,
    ( spl13_21
    | spl13_37
    | spl13_39 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl13_21
    | ~ spl13_37
    | ~ spl13_39 ),
    inference(subsumption_resolution,[],[f281,f188])).

fof(f281,plain,
    ( k2_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(sK2)
    | ~ spl13_37
    | ~ spl13_39 ),
    inference(subsumption_resolution,[],[f280,f275])).

fof(f276,plain,
    ( ~ spl13_37
    | ~ spl13_39
    | spl13_21 ),
    inference(avatar_split_clause,[],[f195,f187,f274,f268])).

fof(f195,plain,
    ( ~ r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r2_hidden(sK9(k2_relset_1(sK1,sK0,k4_relat_1(sK2)),k1_relat_1(sK2)),k2_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_21 ),
    inference(extensionality_resolution,[],[f71,f188])).

fof(f263,plain,
    ( spl13_34
    | ~ spl13_0 ),
    inference(avatar_split_clause,[],[f180,f96,f261])).

fof(f180,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl13_0 ),
    inference(resolution,[],[f60,f97])).

fof(f255,plain,
    ( spl13_15
    | spl13_31
    | spl13_33 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl13_15
    | ~ spl13_31
    | ~ spl13_33 ),
    inference(subsumption_resolution,[],[f253,f168])).

fof(f253,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(sK2)
    | ~ spl13_31
    | ~ spl13_33 ),
    inference(subsumption_resolution,[],[f251,f241])).

fof(f248,plain,
    ( ~ spl13_31
    | ~ spl13_33
    | spl13_15 ),
    inference(avatar_split_clause,[],[f194,f167,f246,f240])).

fof(f194,plain,
    ( ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ r2_hidden(sK9(k2_relat_1(sK2),k1_relset_1(sK1,sK0,k4_relat_1(sK2))),k2_relat_1(sK2))
    | ~ spl13_15 ),
    inference(extensionality_resolution,[],[f71,f168])).

fof(f235,plain,
    ( spl13_28
    | ~ spl13_0 ),
    inference(avatar_split_clause,[],[f160,f96,f233])).

fof(f160,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl13_0 ),
    inference(resolution,[],[f59,f97])).

fof(f227,plain,
    ( spl13_15
    | spl13_23
    | spl13_25 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl13_15
    | ~ spl13_23
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f225,f168])).

fof(f225,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(sK2)
    | ~ spl13_23
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f224,f212])).

fof(f224,plain,
    ( r2_hidden(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k2_relat_1(sK2)
    | ~ spl13_23 ),
    inference(resolution,[],[f206,f70])).

fof(f206,plain,
    ( ~ r2_hidden(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_23 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl13_23
  <=> ~ r2_hidden(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relset_1(sK1,sK0,k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).

fof(f220,plain,
    ( spl13_26
    | ~ spl13_0 ),
    inference(avatar_split_clause,[],[f135,f96,f218])).

fof(f135,plain,
    ( k3_relset_1(sK0,sK1,sK2) = k4_relat_1(sK2)
    | ~ spl13_0 ),
    inference(resolution,[],[f58,f97])).

fof(f213,plain,
    ( ~ spl13_23
    | ~ spl13_25
    | spl13_15 ),
    inference(avatar_split_clause,[],[f193,f167,f211,f205])).

fof(f193,plain,
    ( ~ r2_hidden(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ r2_hidden(sK9(k1_relset_1(sK1,sK0,k4_relat_1(sK2)),k2_relat_1(sK2)),k1_relset_1(sK1,sK0,k4_relat_1(sK2)))
    | ~ spl13_15 ),
    inference(extensionality_resolution,[],[f71,f168])).

fof(f189,plain,
    ( ~ spl13_21
    | ~ spl13_0
    | spl13_9 ),
    inference(avatar_split_clause,[],[f182,f143,f96,f187])).

fof(f143,plain,
    ( spl13_9
  <=> k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f182,plain,
    ( k2_relset_1(sK1,sK0,k4_relat_1(sK2)) != k1_relat_1(sK2)
    | ~ spl13_0
    | ~ spl13_9 ),
    inference(backward_demodulation,[],[f180,f144])).

fof(f144,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f179,plain,
    ( ~ spl13_17
    | spl13_18
    | ~ spl13_0 ),
    inference(avatar_split_clause,[],[f115,f96,f177,f174])).

fof(f174,plain,
    ( spl13_17
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f177,plain,
    ( spl13_18
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl13_0 ),
    inference(resolution,[],[f80,f97])).

fof(f169,plain,
    ( ~ spl13_15
    | ~ spl13_0
    | spl13_13 ),
    inference(avatar_split_clause,[],[f162,f157,f96,f167])).

fof(f157,plain,
    ( spl13_13
  <=> k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f162,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relat_1(sK2)
    | ~ spl13_0
    | ~ spl13_13 ),
    inference(backward_demodulation,[],[f160,f158])).

fof(f158,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relset_1(sK0,sK1,sK2)
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f157])).

fof(f159,plain,
    ( ~ spl13_13
    | ~ spl13_0
    | spl13_5 ),
    inference(avatar_split_clause,[],[f138,f109,f96,f157])).

fof(f109,plain,
    ( spl13_5
  <=> k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f138,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) != k2_relset_1(sK0,sK1,sK2)
    | ~ spl13_0
    | ~ spl13_5 ),
    inference(backward_demodulation,[],[f135,f110])).

fof(f110,plain,
    ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2)
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f152,plain,
    ( spl13_10
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f131,f122,f150])).

fof(f131,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = sK2
    | ~ spl13_6 ),
    inference(resolution,[],[f123,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',involutiveness_k4_relat_1)).

fof(f145,plain,
    ( ~ spl13_9
    | ~ spl13_0
    | spl13_3 ),
    inference(avatar_split_clause,[],[f137,f103,f96,f143])).

fof(f103,plain,
    ( spl13_3
  <=> k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f137,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k4_relat_1(sK2))
    | ~ spl13_0
    | ~ spl13_3 ),
    inference(backward_demodulation,[],[f135,f104])).

fof(f104,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2))
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f124,plain,
    ( spl13_6
    | ~ spl13_0 ),
    inference(avatar_split_clause,[],[f112,f96,f122])).

fof(f112,plain,
    ( v1_relat_1(sK2)
    | ~ spl13_0 ),
    inference(resolution,[],[f82,f97])).

fof(f111,plain,
    ( ~ spl13_3
    | ~ spl13_5 ),
    inference(avatar_split_clause,[],[f55,f109,f103])).

fof(f55,plain,
    ( k1_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) != k2_relset_1(sK0,sK1,sK2)
    | k1_relset_1(sK0,sK1,sK2) != k2_relset_1(sK1,sK0,k3_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        | k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) != k2_relset_1(X0,X1,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
          & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t24_relset_1.p',t24_relset_1)).

fof(f98,plain,(
    spl13_0 ),
    inference(avatar_split_clause,[],[f56,f96])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
