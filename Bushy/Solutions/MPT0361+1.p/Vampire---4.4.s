%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t41_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:23 EDT 2019

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  667 (2315 expanded)
%              Number of leaves         :  159 ( 944 expanded)
%              Depth                    :   10
%              Number of atoms          : 1709 (5512 expanded)
%              Number of equality atoms :  268 ( 856 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3494,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f91,f98,f105,f132,f143,f154,f161,f168,f181,f188,f198,f208,f220,f228,f235,f243,f266,f278,f296,f317,f324,f331,f350,f375,f417,f435,f450,f483,f494,f501,f510,f529,f544,f551,f561,f605,f613,f710,f717,f724,f732,f751,f758,f777,f800,f807,f818,f841,f861,f869,f888,f907,f926,f933,f951,f958,f971,f1043,f1050,f1057,f1087,f1094,f1111,f1130,f1227,f1236,f1295,f1316,f1325,f1346,f1367,f1388,f1409,f1416,f1436,f1443,f1473,f1564,f1571,f1578,f1606,f1683,f1692,f1707,f1710,f1735,f1743,f1768,f1776,f1860,f1867,f1880,f1883,f1909,f1917,f1943,f1951,f1977,f1984,f2007,f2014,f2021,f2044,f2246,f2253,f2264,f2291,f2299,f2328,f2410,f2417,f2424,f2431,f2478,f2486,f2493,f2523,f2551,f2559,f2587,f2595,f2603,f2631,f2659,f2667,f3055,f3184,f3312,f3321,f3329,f3337,f3345,f3352,f3363,f3371,f3381,f3417,f3425,f3461,f3489])).

fof(f3489,plain,
    ( ~ spl4_4
    | ~ spl4_52
    | spl4_55 ),
    inference(avatar_contradiction_clause,[],[f3488])).

fof(f3488,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_52
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f3487,f97])).

fof(f97,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f3487,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_52
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f3463,f434])).

fof(f434,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl4_52
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f3463,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_55 ),
    inference(resolution,[],[f819,f449])).

fof(f449,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f448])).

fof(f448,plain,
    ( spl4_55
  <=> ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f819,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k2_xboole_0(X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f69,f64])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',t7_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',t31_subset_1)).

fof(f3461,plain,
    ( spl4_278
    | ~ spl4_4
    | ~ spl4_276 ),
    inference(avatar_split_clause,[],[f3426,f3423,f96,f3459])).

fof(f3459,plain,
    ( spl4_278
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_278])])).

fof(f3423,plain,
    ( spl4_276
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_276])])).

fof(f3426,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_276 ),
    inference(resolution,[],[f3424,f244])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | m1_subset_1(k4_subset_1(sK0,sK1,X0),k1_zfmisc_1(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f73,f97])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',dt_k4_subset_1)).

fof(f3424,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_276 ),
    inference(avatar_component_clause,[],[f3423])).

fof(f3425,plain,
    ( spl4_276
    | ~ spl4_4
    | ~ spl4_272
    | ~ spl4_274 ),
    inference(avatar_split_clause,[],[f3418,f3415,f3379,f96,f3423])).

fof(f3379,plain,
    ( spl4_272
  <=> m1_subset_1(k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_272])])).

fof(f3415,plain,
    ( spl4_274
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_274])])).

fof(f3418,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_272
    | ~ spl4_274 ),
    inference(forward_demodulation,[],[f3416,f3385])).

fof(f3385,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))) = k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))))
    | ~ spl4_4
    | ~ spl4_272 ),
    inference(resolution,[],[f3380,f377])).

fof(f377,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k2_xboole_0(sK1,X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f74,f97])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',redefinition_k4_subset_1)).

fof(f3380,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_272 ),
    inference(avatar_component_clause,[],[f3379])).

fof(f3416,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_274 ),
    inference(avatar_component_clause,[],[f3415])).

fof(f3417,plain,
    ( spl4_274
    | ~ spl4_4
    | ~ spl4_272 ),
    inference(avatar_split_clause,[],[f3382,f3379,f96,f3415])).

fof(f3382,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_272 ),
    inference(resolution,[],[f3380,f244])).

fof(f3381,plain,
    ( spl4_272
    | ~ spl4_6
    | ~ spl4_270 ),
    inference(avatar_split_clause,[],[f3374,f3369,f103,f3379])).

fof(f103,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f3369,plain,
    ( spl4_270
  <=> k4_subset_1(sK0,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))),sK2) = k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_270])])).

fof(f3374,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_6
    | ~ spl4_270 ),
    inference(subsumption_resolution,[],[f3373,f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',existence_m1_subset_1)).

fof(f3373,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl4_6
    | ~ spl4_270 ),
    inference(subsumption_resolution,[],[f3372,f104])).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f3372,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl4_270 ),
    inference(superposition,[],[f246,f3370])).

fof(f3370,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))),sK2) = k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_270 ),
    inference(avatar_component_clause,[],[f3369])).

fof(f246,plain,(
    ! [X4,X2,X3] :
      ( m1_subset_1(k4_subset_1(X3,k3_subset_1(X3,X4),X2),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f73,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',dt_k3_subset_1)).

fof(f3371,plain,
    ( spl4_270
    | ~ spl4_6
    | ~ spl4_210 ),
    inference(avatar_split_clause,[],[f3305,f2251,f103,f3369])).

fof(f2251,plain,
    ( spl4_210
  <=> k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))) = k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_210])])).

fof(f3305,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))),sK2) = k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_6
    | ~ spl4_210 ),
    inference(forward_demodulation,[],[f3249,f2252])).

fof(f2252,plain,
    ( k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))) = k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_210 ),
    inference(avatar_component_clause,[],[f2251])).

fof(f3249,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))),sK2) = k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_6 ),
    inference(resolution,[],[f680,f62])).

fof(f680,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,k3_subset_1(sK0,X4),sK2) = k4_subset_1(sK0,sK2,k3_subset_1(sK0,X4)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f585,f66])).

fof(f585,plain,
    ( ! [X18] :
        ( ~ m1_subset_1(X18,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,X18,sK2) = k4_subset_1(sK0,sK2,X18) )
    | ~ spl4_6 ),
    inference(resolution,[],[f75,f104])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',commutativity_k4_subset_1)).

fof(f3363,plain,
    ( spl4_268
    | ~ spl4_4
    | ~ spl4_208 ),
    inference(avatar_split_clause,[],[f3048,f2244,f96,f3361])).

fof(f3361,plain,
    ( spl4_268
  <=> k4_subset_1(sK0,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))),sK1) = k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_268])])).

fof(f2244,plain,
    ( spl4_208
  <=> k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))) = k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_208])])).

fof(f3048,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))),sK1) = k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_4
    | ~ spl4_208 ),
    inference(forward_demodulation,[],[f2992,f2245])).

fof(f2245,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))) = k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_208 ),
    inference(avatar_component_clause,[],[f2244])).

fof(f2992,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))),sK1) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_4 ),
    inference(resolution,[],[f640,f62])).

fof(f640,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,k3_subset_1(sK0,X4),sK1) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,X4)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f584,f66])).

fof(f584,plain,
    ( ! [X17] :
        ( ~ m1_subset_1(X17,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,X17,sK1) = k4_subset_1(sK0,sK1,X17) )
    | ~ spl4_4 ),
    inference(resolution,[],[f75,f97])).

fof(f3352,plain,
    ( spl4_266
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f2112,f415,f264,f3350])).

fof(f3350,plain,
    ( spl4_266
  <=> k4_subset_1(sK0,sK3(k1_zfmisc_1(sK0)),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_266])])).

fof(f264,plain,
    ( spl4_34
  <=> m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f415,plain,
    ( spl4_50
  <=> k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f2112,plain,
    ( k4_subset_1(sK0,sK3(k1_zfmisc_1(sK0)),k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f2111,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',commutativity_k2_xboole_0)).

fof(f2111,plain,
    ( k4_subset_1(sK0,sK3(k1_zfmisc_1(sK0)),k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK3(k1_zfmisc_1(sK0)),k2_xboole_0(sK1,sK2))
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f2065,f416])).

fof(f416,plain,
    ( k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f415])).

fof(f2065,plain,
    ( k4_subset_1(sK0,sK3(k1_zfmisc_1(sK0)),k4_subset_1(sK0,sK1,sK2)) = k2_xboole_0(sK3(k1_zfmisc_1(sK0)),k4_subset_1(sK0,sK1,sK2))
    | ~ spl4_34 ),
    inference(resolution,[],[f390,f265])).

fof(f265,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f264])).

fof(f390,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | k4_subset_1(X20,sK3(k1_zfmisc_1(X20)),X19) = k2_xboole_0(sK3(k1_zfmisc_1(X20)),X19) ) ),
    inference(resolution,[],[f74,f62])).

fof(f3345,plain,
    ( spl4_264
    | ~ spl4_36
    | ~ spl4_58
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1531,f931,f492,f276,f3343])).

fof(f3343,plain,
    ( spl4_264
  <=> k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_264])])).

fof(f276,plain,
    ( spl4_36
  <=> m1_subset_1(k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f492,plain,
    ( spl4_58
  <=> k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f931,plain,
    ( spl4_108
  <=> k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f1531,plain,
    ( k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))))
    | ~ spl4_36
    | ~ spl4_58
    | ~ spl4_108 ),
    inference(forward_demodulation,[],[f1530,f932])).

fof(f932,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_108 ),
    inference(avatar_component_clause,[],[f931])).

fof(f1530,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))))
    | ~ spl4_36
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f1488,f493])).

fof(f493,plain,
    ( k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f492])).

fof(f1488,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))))) = k4_xboole_0(sK0,k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0)))))
    | ~ spl4_36 ),
    inference(resolution,[],[f173,f277])).

fof(f277,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f276])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = k4_xboole_0(X0,k3_subset_1(X0,X1)) ) ),
    inference(resolution,[],[f68,f66])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',d5_subset_1)).

fof(f3337,plain,
    ( spl4_262
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f282,f276,f3335])).

fof(f3335,plain,
    ( spl4_262
  <=> k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))) = k3_subset_1(sK0,k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_262])])).

fof(f282,plain,
    ( k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))) = k3_subset_1(sK0,k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0)))))
    | ~ spl4_36 ),
    inference(resolution,[],[f277,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',involutiveness_k3_subset_1)).

fof(f3329,plain,
    ( spl4_260
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f281,f276,f3327])).

fof(f3327,plain,
    ( spl4_260
  <=> k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0)))) = k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_260])])).

fof(f281,plain,
    ( k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0)))) = k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_36 ),
    inference(resolution,[],[f277,f68])).

fof(f3321,plain,
    ( spl4_258
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_166 ),
    inference(avatar_split_clause,[],[f3303,f1690,f103,f96,f3319])).

fof(f3319,plain,
    ( spl4_258
  <=> k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) = k2_xboole_0(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_258])])).

fof(f1690,plain,
    ( spl4_166
  <=> k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK1)) = k2_xboole_0(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_166])])).

fof(f3303,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) = k2_xboole_0(sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_166 ),
    inference(forward_demodulation,[],[f3244,f1691])).

fof(f1691,plain,
    ( k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK1)) = k2_xboole_0(sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_166 ),
    inference(avatar_component_clause,[],[f1690])).

fof(f3244,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK2) = k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f680,f97])).

fof(f3312,plain,
    ( spl4_256
    | ~ spl4_6
    | ~ spl4_164 ),
    inference(avatar_split_clause,[],[f3304,f1681,f103,f3310])).

fof(f3310,plain,
    ( spl4_256
  <=> k4_subset_1(sK0,k3_subset_1(sK0,sK2),sK2) = k2_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_256])])).

fof(f1681,plain,
    ( spl4_164
  <=> k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK2)) = k2_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).

fof(f3304,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK2),sK2) = k2_xboole_0(sK2,k3_subset_1(sK0,sK2))
    | ~ spl4_6
    | ~ spl4_164 ),
    inference(forward_demodulation,[],[f3245,f1682])).

fof(f1682,plain,
    ( k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK2)) = k2_xboole_0(sK2,k3_subset_1(sK0,sK2))
    | ~ spl4_164 ),
    inference(avatar_component_clause,[],[f1681])).

fof(f3245,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK2),sK2) = k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f680,f104])).

fof(f3184,plain,
    ( spl4_254
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_136 ),
    inference(avatar_split_clause,[],[f3047,f1314,f103,f96,f3182])).

fof(f3182,plain,
    ( spl4_254
  <=> k4_subset_1(sK0,k3_subset_1(sK0,sK2),sK1) = k2_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_254])])).

fof(f1314,plain,
    ( spl4_136
  <=> k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) = k2_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_136])])).

fof(f3047,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK2),sK1) = k2_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_136 ),
    inference(forward_demodulation,[],[f2988,f1315])).

fof(f1315,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) = k2_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_136 ),
    inference(avatar_component_clause,[],[f1314])).

fof(f2988,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK2),sK1) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f640,f104])).

fof(f3055,plain,
    ( spl4_252
    | ~ spl4_4
    | ~ spl4_130 ),
    inference(avatar_split_clause,[],[f3046,f1225,f96,f3053])).

fof(f3053,plain,
    ( spl4_252
  <=> k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_252])])).

fof(f1225,plain,
    ( spl4_130
  <=> k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).

fof(f3046,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_130 ),
    inference(forward_demodulation,[],[f2987,f1226])).

fof(f1226,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_130 ),
    inference(avatar_component_clause,[],[f1225])).

fof(f2987,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f640,f97])).

fof(f2667,plain,
    ( spl4_250
    | ~ spl4_4
    | ~ spl4_238
    | ~ spl4_248 ),
    inference(avatar_split_clause,[],[f2660,f2657,f2557,f96,f2665])).

fof(f2665,plain,
    ( spl4_250
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_250])])).

fof(f2557,plain,
    ( spl4_238
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_238])])).

fof(f2657,plain,
    ( spl4_248
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_248])])).

fof(f2660,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_238
    | ~ spl4_248 ),
    inference(forward_demodulation,[],[f2658,f2561])).

fof(f2561,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0)))))
    | ~ spl4_4
    | ~ spl4_238 ),
    inference(resolution,[],[f2558,f377])).

fof(f2558,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_238 ),
    inference(avatar_component_clause,[],[f2557])).

fof(f2658,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_248 ),
    inference(avatar_component_clause,[],[f2657])).

fof(f2659,plain,
    ( spl4_248
    | ~ spl4_4
    | ~ spl4_238 ),
    inference(avatar_split_clause,[],[f2560,f2557,f96,f2657])).

fof(f2560,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_238 ),
    inference(resolution,[],[f2558,f244])).

fof(f2631,plain,
    ( spl4_246
    | ~ spl4_4
    | ~ spl4_194
    | ~ spl4_242 ),
    inference(avatar_split_clause,[],[f2596,f2593,f1949,f96,f2629])).

fof(f2629,plain,
    ( spl4_246
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_246])])).

fof(f1949,plain,
    ( spl4_194
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).

fof(f2593,plain,
    ( spl4_242
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_242])])).

fof(f2596,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_194
    | ~ spl4_242 ),
    inference(forward_demodulation,[],[f2594,f1953])).

fof(f1953,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))))
    | ~ spl4_4
    | ~ spl4_194 ),
    inference(resolution,[],[f1950,f377])).

fof(f1950,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))),k1_zfmisc_1(sK0))
    | ~ spl4_194 ),
    inference(avatar_component_clause,[],[f1949])).

fof(f2594,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))))),k1_zfmisc_1(sK0))
    | ~ spl4_242 ),
    inference(avatar_component_clause,[],[f2593])).

fof(f2603,plain,
    ( spl4_244
    | ~ spl4_4
    | ~ spl4_178
    | ~ spl4_240 ),
    inference(avatar_split_clause,[],[f2588,f2585,f1774,f96,f2601])).

fof(f2601,plain,
    ( spl4_244
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_244])])).

fof(f1774,plain,
    ( spl4_178
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_178])])).

fof(f2585,plain,
    ( spl4_240
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_240])])).

fof(f2588,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_178
    | ~ spl4_240 ),
    inference(forward_demodulation,[],[f2586,f1778])).

fof(f1778,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))))
    | ~ spl4_4
    | ~ spl4_178 ),
    inference(resolution,[],[f1775,f377])).

fof(f1775,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))),k1_zfmisc_1(sK0))
    | ~ spl4_178 ),
    inference(avatar_component_clause,[],[f1774])).

fof(f2586,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))))),k1_zfmisc_1(sK0))
    | ~ spl4_240 ),
    inference(avatar_component_clause,[],[f2585])).

fof(f2595,plain,
    ( spl4_242
    | ~ spl4_4
    | ~ spl4_194 ),
    inference(avatar_split_clause,[],[f1952,f1949,f96,f2593])).

fof(f1952,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_194 ),
    inference(resolution,[],[f1950,f244])).

fof(f2587,plain,
    ( spl4_240
    | ~ spl4_4
    | ~ spl4_178 ),
    inference(avatar_split_clause,[],[f1777,f1774,f96,f2585])).

fof(f1777,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_178 ),
    inference(resolution,[],[f1775,f244])).

fof(f2559,plain,
    ( spl4_238
    | ~ spl4_4
    | ~ spl4_234
    | ~ spl4_236 ),
    inference(avatar_split_clause,[],[f2552,f2549,f2521,f96,f2557])).

fof(f2521,plain,
    ( spl4_234
  <=> m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_234])])).

fof(f2549,plain,
    ( spl4_236
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_236])])).

fof(f2552,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_234
    | ~ spl4_236 ),
    inference(forward_demodulation,[],[f2550,f2525])).

fof(f2525,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0)))) = k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_4
    | ~ spl4_234 ),
    inference(resolution,[],[f2522,f377])).

fof(f2522,plain,
    ( m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0))
    | ~ spl4_234 ),
    inference(avatar_component_clause,[],[f2521])).

fof(f2550,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_236 ),
    inference(avatar_component_clause,[],[f2549])).

fof(f2551,plain,
    ( spl4_236
    | ~ spl4_4
    | ~ spl4_234 ),
    inference(avatar_split_clause,[],[f2524,f2521,f96,f2549])).

fof(f2524,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_234 ),
    inference(resolution,[],[f2522,f244])).

fof(f2523,plain,
    ( spl4_234
    | ~ spl4_34
    | ~ spl4_50
    | ~ spl4_230 ),
    inference(avatar_split_clause,[],[f2516,f2484,f415,f264,f2521])).

fof(f2484,plain,
    ( spl4_230
  <=> k4_subset_1(sK0,k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_230])])).

fof(f2516,plain,
    ( m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0))
    | ~ spl4_34
    | ~ spl4_50
    | ~ spl4_230 ),
    inference(subsumption_resolution,[],[f2515,f62])).

fof(f2515,plain,
    ( m1_subset_1(k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl4_34
    | ~ spl4_50
    | ~ spl4_230 ),
    inference(superposition,[],[f420,f2485])).

fof(f2485,plain,
    ( k4_subset_1(sK0,k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_230 ),
    inference(avatar_component_clause,[],[f2484])).

fof(f420,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_subset_1(sK0,k2_xboole_0(sK1,sK2),X0),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(superposition,[],[f268,f416])).

fof(f268,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_subset_1(sK0,k4_subset_1(sK0,sK1,sK2),X0),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_34 ),
    inference(resolution,[],[f265,f73])).

fof(f2493,plain,
    ( spl4_232
    | ~ spl4_4
    | ~ spl4_216
    | ~ spl4_228 ),
    inference(avatar_split_clause,[],[f2479,f2476,f2297,f96,f2491])).

fof(f2491,plain,
    ( spl4_232
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_232])])).

fof(f2297,plain,
    ( spl4_216
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_216])])).

fof(f2476,plain,
    ( spl4_228
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_228])])).

fof(f2479,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_216
    | ~ spl4_228 ),
    inference(forward_demodulation,[],[f2477,f2301])).

fof(f2301,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))))
    | ~ spl4_4
    | ~ spl4_216 ),
    inference(resolution,[],[f2298,f377])).

fof(f2298,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_216 ),
    inference(avatar_component_clause,[],[f2297])).

fof(f2477,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0))
    | ~ spl4_228 ),
    inference(avatar_component_clause,[],[f2476])).

fof(f2486,plain,
    ( spl4_230
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f2388,f433,f2484])).

fof(f2388,plain,
    ( k4_subset_1(sK0,k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0))) = k2_xboole_0(k2_xboole_0(sK1,sK2),sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_52 ),
    inference(resolution,[],[f438,f62])).

fof(f438,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,k2_xboole_0(sK1,sK2),X0) = k2_xboole_0(k2_xboole_0(sK1,sK2),X0) )
    | ~ spl4_52 ),
    inference(resolution,[],[f434,f74])).

fof(f2478,plain,
    ( spl4_228
    | ~ spl4_4
    | ~ spl4_216 ),
    inference(avatar_split_clause,[],[f2300,f2297,f96,f2476])).

fof(f2300,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_216 ),
    inference(resolution,[],[f2298,f244])).

fof(f2431,plain,
    ( spl4_226
    | ~ spl4_94
    | ~ spl4_124 ),
    inference(avatar_split_clause,[],[f1552,f1092,f816,f2429])).

fof(f2429,plain,
    ( spl4_226
  <=> k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_226])])).

fof(f816,plain,
    ( spl4_94
  <=> m1_subset_1(k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f1092,plain,
    ( spl4_124
  <=> k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f1552,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))
    | ~ spl4_94
    | ~ spl4_124 ),
    inference(forward_demodulation,[],[f1510,f1093])).

fof(f1093,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl4_124 ),
    inference(avatar_component_clause,[],[f1092])).

fof(f1510,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))
    | ~ spl4_94 ),
    inference(resolution,[],[f173,f817])).

fof(f817,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f816])).

fof(f2424,plain,
    ( spl4_224
    | ~ spl4_138
    | ~ spl4_150 ),
    inference(avatar_split_clause,[],[f1533,f1434,f1323,f2422])).

fof(f2422,plain,
    ( spl4_224
  <=> k2_xboole_0(sK1,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_224])])).

fof(f1323,plain,
    ( spl4_138
  <=> m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).

fof(f1434,plain,
    ( spl4_150
  <=> k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))) = k2_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).

fof(f1533,plain,
    ( k2_xboole_0(sK1,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))))
    | ~ spl4_138
    | ~ spl4_150 ),
    inference(forward_demodulation,[],[f1491,f1435])).

fof(f1435,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))) = k2_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_150 ),
    inference(avatar_component_clause,[],[f1434])).

fof(f1491,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))))
    | ~ spl4_138 ),
    inference(resolution,[],[f173,f1324])).

fof(f1324,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_138 ),
    inference(avatar_component_clause,[],[f1323])).

fof(f2417,plain,
    ( spl4_222
    | ~ spl4_132
    | ~ spl4_146 ),
    inference(avatar_split_clause,[],[f1532,f1407,f1234,f2415])).

fof(f2415,plain,
    ( spl4_222
  <=> k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_222])])).

fof(f1234,plain,
    ( spl4_132
  <=> m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_132])])).

fof(f1407,plain,
    ( spl4_146
  <=> k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_146])])).

fof(f1532,plain,
    ( k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))))
    | ~ spl4_132
    | ~ spl4_146 ),
    inference(forward_demodulation,[],[f1490,f1408])).

fof(f1408,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_146 ),
    inference(avatar_component_clause,[],[f1407])).

fof(f1490,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))))
    | ~ spl4_132 ),
    inference(resolution,[],[f173,f1235])).

fof(f1235,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_132 ),
    inference(avatar_component_clause,[],[f1234])).

fof(f2410,plain,
    ( spl4_220
    | ~ spl4_64
    | ~ spl4_112 ),
    inference(avatar_split_clause,[],[f1551,f956,f527,f2408])).

fof(f2408,plain,
    ( spl4_220
  <=> k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_220])])).

fof(f527,plain,
    ( spl4_64
  <=> m1_subset_1(k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f956,plain,
    ( spl4_112
  <=> k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f1551,plain,
    ( k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))))
    | ~ spl4_64
    | ~ spl4_112 ),
    inference(forward_demodulation,[],[f1509,f957])).

fof(f957,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_112 ),
    inference(avatar_component_clause,[],[f956])).

fof(f1509,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))))
    | ~ spl4_64 ),
    inference(resolution,[],[f173,f528])).

fof(f528,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f527])).

fof(f2328,plain,
    ( spl4_218
    | ~ spl4_4
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f332,f329,f96,f2326])).

fof(f2326,plain,
    ( spl4_218
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_218])])).

fof(f329,plain,
    ( spl4_44
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f332,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_44 ),
    inference(resolution,[],[f330,f244])).

fof(f330,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f329])).

fof(f2299,plain,
    ( spl4_216
    | ~ spl4_4
    | ~ spl4_212
    | ~ spl4_214 ),
    inference(avatar_split_clause,[],[f2292,f2289,f2262,f96,f2297])).

fof(f2262,plain,
    ( spl4_212
  <=> m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_212])])).

fof(f2289,plain,
    ( spl4_214
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_214])])).

fof(f2292,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_212
    | ~ spl4_214 ),
    inference(forward_demodulation,[],[f2290,f2266])).

fof(f2266,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))))
    | ~ spl4_4
    | ~ spl4_212 ),
    inference(resolution,[],[f2263,f377])).

fof(f2263,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_212 ),
    inference(avatar_component_clause,[],[f2262])).

fof(f2290,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_214 ),
    inference(avatar_component_clause,[],[f2289])).

fof(f2291,plain,
    ( spl4_214
    | ~ spl4_4
    | ~ spl4_208 ),
    inference(avatar_split_clause,[],[f2256,f2244,f96,f2289])).

fof(f2256,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_208 ),
    inference(subsumption_resolution,[],[f2254,f62])).

fof(f2254,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_208 ),
    inference(superposition,[],[f302,f2245])).

fof(f302,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,k3_subset_1(sK0,X0))),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f257,f244])).

fof(f257,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_subset_1(sK0,sK1,k3_subset_1(sK0,X0)),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f244,f66])).

fof(f2264,plain,
    ( spl4_212
    | ~ spl4_4
    | ~ spl4_208 ),
    inference(avatar_split_clause,[],[f2257,f2244,f96,f2262])).

fof(f2257,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_208 ),
    inference(subsumption_resolution,[],[f2255,f62])).

fof(f2255,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_208 ),
    inference(superposition,[],[f257,f2245])).

fof(f2253,plain,
    ( spl4_210
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1666,f103,f2251])).

fof(f1666,plain,
    ( k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))) = k2_xboole_0(sK2,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_6 ),
    inference(resolution,[],[f463,f62])).

fof(f463,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK2,k3_subset_1(sK0,X4)) = k2_xboole_0(sK2,k3_subset_1(sK0,X4)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f378,f66])).

fof(f378,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK2,X1) = k2_xboole_0(sK2,X1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f74,f104])).

fof(f2246,plain,
    ( spl4_208
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1210,f96,f2244])).

fof(f1210,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0)))) = k2_xboole_0(sK1,k3_subset_1(sK0,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_4 ),
    inference(resolution,[],[f403,f62])).

fof(f403,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,k3_subset_1(sK0,X4)) = k2_xboole_0(sK1,k3_subset_1(sK0,X4)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f377,f66])).

fof(f2044,plain,
    ( spl4_206
    | ~ spl4_186 ),
    inference(avatar_split_clause,[],[f1902,f1878,f2042])).

fof(f2042,plain,
    ( spl4_206
  <=> k2_xboole_0(sK2,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_206])])).

fof(f1878,plain,
    ( spl4_186
  <=> m1_subset_1(k2_xboole_0(sK2,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_186])])).

fof(f1902,plain,
    ( k2_xboole_0(sK2,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))))
    | ~ spl4_186 ),
    inference(forward_demodulation,[],[f1899,f1891])).

fof(f1891,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))) = k2_xboole_0(sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_186 ),
    inference(resolution,[],[f1879,f67])).

fof(f1879,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_186 ),
    inference(avatar_component_clause,[],[f1878])).

fof(f1899,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))))
    | ~ spl4_186 ),
    inference(resolution,[],[f1879,f173])).

fof(f2021,plain,
    ( spl4_204
    | ~ spl4_186 ),
    inference(avatar_split_clause,[],[f1892,f1878,f2019])).

fof(f2019,plain,
    ( spl4_204
  <=> k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))) = k4_xboole_0(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_204])])).

fof(f1892,plain,
    ( k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))) = k4_xboole_0(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))
    | ~ spl4_186 ),
    inference(resolution,[],[f1879,f68])).

fof(f2014,plain,
    ( spl4_202
    | ~ spl4_186 ),
    inference(avatar_split_clause,[],[f1891,f1878,f2012])).

fof(f2012,plain,
    ( spl4_202
  <=> k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))) = k2_xboole_0(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_202])])).

fof(f2007,plain,
    ( spl4_200
    | ~ spl4_170 ),
    inference(avatar_split_clause,[],[f1728,f1705,f2005])).

fof(f2005,plain,
    ( spl4_200
  <=> k2_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_200])])).

fof(f1705,plain,
    ( spl4_170
  <=> m1_subset_1(k2_xboole_0(sK2,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).

fof(f1728,plain,
    ( k2_xboole_0(sK2,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))))
    | ~ spl4_170 ),
    inference(forward_demodulation,[],[f1725,f1718])).

fof(f1718,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))) = k2_xboole_0(sK2,k3_subset_1(sK0,sK2))
    | ~ spl4_170 ),
    inference(resolution,[],[f1706,f67])).

fof(f1706,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_170 ),
    inference(avatar_component_clause,[],[f1705])).

fof(f1725,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))))
    | ~ spl4_170 ),
    inference(resolution,[],[f1706,f173])).

fof(f1984,plain,
    ( spl4_198
    | ~ spl4_170 ),
    inference(avatar_split_clause,[],[f1719,f1705,f1982])).

fof(f1982,plain,
    ( spl4_198
  <=> k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_198])])).

fof(f1719,plain,
    ( k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))
    | ~ spl4_170 ),
    inference(resolution,[],[f1706,f68])).

fof(f1977,plain,
    ( spl4_196
    | ~ spl4_170 ),
    inference(avatar_split_clause,[],[f1718,f1705,f1975])).

fof(f1975,plain,
    ( spl4_196
  <=> k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))) = k2_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_196])])).

fof(f1951,plain,
    ( spl4_194
    | ~ spl4_4
    | ~ spl4_190
    | ~ spl4_192 ),
    inference(avatar_split_clause,[],[f1944,f1941,f1915,f96,f1949])).

fof(f1915,plain,
    ( spl4_190
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_190])])).

fof(f1941,plain,
    ( spl4_192
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).

fof(f1944,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_190
    | ~ spl4_192 ),
    inference(forward_demodulation,[],[f1942,f1919])).

fof(f1919,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_190 ),
    inference(resolution,[],[f1916,f377])).

fof(f1916,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))),k1_zfmisc_1(sK0))
    | ~ spl4_190 ),
    inference(avatar_component_clause,[],[f1915])).

fof(f1942,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))),k1_zfmisc_1(sK0))
    | ~ spl4_192 ),
    inference(avatar_component_clause,[],[f1941])).

fof(f1943,plain,
    ( spl4_192
    | ~ spl4_4
    | ~ spl4_190 ),
    inference(avatar_split_clause,[],[f1918,f1915,f96,f1941])).

fof(f1918,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_190 ),
    inference(resolution,[],[f1916,f244])).

fof(f1917,plain,
    ( spl4_190
    | ~ spl4_4
    | ~ spl4_186
    | ~ spl4_188 ),
    inference(avatar_split_clause,[],[f1910,f1907,f1878,f96,f1915])).

fof(f1907,plain,
    ( spl4_188
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_188])])).

fof(f1910,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_186
    | ~ spl4_188 ),
    inference(forward_demodulation,[],[f1908,f1885])).

fof(f1885,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))) = k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_186 ),
    inference(resolution,[],[f1879,f377])).

fof(f1908,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))),k1_zfmisc_1(sK0))
    | ~ spl4_188 ),
    inference(avatar_component_clause,[],[f1907])).

fof(f1909,plain,
    ( spl4_188
    | ~ spl4_4
    | ~ spl4_186 ),
    inference(avatar_split_clause,[],[f1884,f1878,f96,f1907])).

fof(f1884,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_186 ),
    inference(resolution,[],[f1879,f244])).

fof(f1883,plain,
    ( ~ spl4_4
    | spl4_185 ),
    inference(avatar_contradiction_clause,[],[f1882])).

fof(f1882,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_185 ),
    inference(subsumption_resolution,[],[f1881,f97])).

fof(f1881,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_185 ),
    inference(resolution,[],[f1873,f66])).

fof(f1873,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_185 ),
    inference(avatar_component_clause,[],[f1872])).

fof(f1872,plain,
    ( spl4_185
  <=> ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_185])])).

fof(f1880,plain,
    ( ~ spl4_185
    | spl4_186
    | ~ spl4_6
    | ~ spl4_166 ),
    inference(avatar_split_clause,[],[f1694,f1690,f103,f1878,f1872])).

fof(f1694,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_6
    | ~ spl4_166 ),
    inference(superposition,[],[f245,f1691])).

fof(f245,plain,
    ( ! [X1] :
        ( m1_subset_1(k4_subset_1(sK0,sK2,X1),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f73,f104])).

fof(f1867,plain,
    ( spl4_182
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1838,f103,f1865])).

fof(f1865,plain,
    ( spl4_182
  <=> k4_subset_1(sK0,k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK2)) = k3_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_182])])).

fof(f1838,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK2)) = k3_subset_1(sK0,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f135,f104])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,k3_subset_1(X0,X1),k3_subset_1(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(resolution,[],[f76,f66])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X1) = X1 ) ),
    inference(condensation,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',idempotence_k4_subset_1)).

fof(f1860,plain,
    ( spl4_180
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1837,f96,f1858])).

fof(f1858,plain,
    ( spl4_180
  <=> k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_180])])).

fof(f1837,plain,
    ( k4_subset_1(sK0,k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f135,f97])).

fof(f1776,plain,
    ( spl4_178
    | ~ spl4_4
    | ~ spl4_174
    | ~ spl4_176 ),
    inference(avatar_split_clause,[],[f1769,f1766,f1741,f96,f1774])).

fof(f1741,plain,
    ( spl4_174
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_174])])).

fof(f1766,plain,
    ( spl4_176
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_176])])).

fof(f1769,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_174
    | ~ spl4_176 ),
    inference(forward_demodulation,[],[f1767,f1745])).

fof(f1745,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))))
    | ~ spl4_4
    | ~ spl4_174 ),
    inference(resolution,[],[f1742,f377])).

fof(f1742,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_174 ),
    inference(avatar_component_clause,[],[f1741])).

fof(f1767,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))),k1_zfmisc_1(sK0))
    | ~ spl4_176 ),
    inference(avatar_component_clause,[],[f1766])).

fof(f1768,plain,
    ( spl4_176
    | ~ spl4_4
    | ~ spl4_174 ),
    inference(avatar_split_clause,[],[f1744,f1741,f96,f1766])).

fof(f1744,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_174 ),
    inference(resolution,[],[f1742,f244])).

fof(f1743,plain,
    ( spl4_174
    | ~ spl4_4
    | ~ spl4_170
    | ~ spl4_172 ),
    inference(avatar_split_clause,[],[f1736,f1733,f1705,f96,f1741])).

fof(f1733,plain,
    ( spl4_172
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_172])])).

fof(f1736,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_170
    | ~ spl4_172 ),
    inference(forward_demodulation,[],[f1734,f1712])).

fof(f1712,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))) = k2_xboole_0(sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2)))
    | ~ spl4_4
    | ~ spl4_170 ),
    inference(resolution,[],[f1706,f377])).

fof(f1734,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_172 ),
    inference(avatar_component_clause,[],[f1733])).

fof(f1735,plain,
    ( spl4_172
    | ~ spl4_4
    | ~ spl4_170 ),
    inference(avatar_split_clause,[],[f1711,f1705,f96,f1733])).

fof(f1711,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k3_subset_1(sK0,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_170 ),
    inference(resolution,[],[f1706,f244])).

fof(f1710,plain,
    ( ~ spl4_6
    | spl4_169 ),
    inference(avatar_contradiction_clause,[],[f1709])).

fof(f1709,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_169 ),
    inference(subsumption_resolution,[],[f1708,f104])).

fof(f1708,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_169 ),
    inference(resolution,[],[f1700,f66])).

fof(f1700,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_169 ),
    inference(avatar_component_clause,[],[f1699])).

fof(f1699,plain,
    ( spl4_169
  <=> ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_169])])).

fof(f1707,plain,
    ( ~ spl4_169
    | spl4_170
    | ~ spl4_6
    | ~ spl4_164 ),
    inference(avatar_split_clause,[],[f1685,f1681,f103,f1705,f1699])).

fof(f1685,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_6
    | ~ spl4_164 ),
    inference(superposition,[],[f245,f1682])).

fof(f1692,plain,
    ( spl4_166
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1662,f103,f96,f1690])).

fof(f1662,plain,
    ( k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK1)) = k2_xboole_0(sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f463,f97])).

fof(f1683,plain,
    ( spl4_164
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1663,f103,f1681])).

fof(f1663,plain,
    ( k4_subset_1(sK0,sK2,k3_subset_1(sK0,sK2)) = k2_xboole_0(sK2,k3_subset_1(sK0,sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f463,f104])).

fof(f1606,plain,
    ( spl4_162
    | ~ spl4_4
    | ~ spl4_144 ),
    inference(avatar_split_clause,[],[f1402,f1386,f96,f1604])).

fof(f1604,plain,
    ( spl4_162
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).

fof(f1386,plain,
    ( spl4_144
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).

fof(f1402,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_144 ),
    inference(forward_demodulation,[],[f1394,f1393])).

fof(f1393,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))))
    | ~ spl4_4
    | ~ spl4_144 ),
    inference(resolution,[],[f1387,f377])).

fof(f1387,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))),k1_zfmisc_1(sK0))
    | ~ spl4_144 ),
    inference(avatar_component_clause,[],[f1386])).

fof(f1394,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_144 ),
    inference(resolution,[],[f1387,f244])).

fof(f1578,plain,
    ( spl4_160
    | ~ spl4_34
    | ~ spl4_50
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f1529,f549,f415,f264,f1576])).

fof(f1576,plain,
    ( spl4_160
  <=> k2_xboole_0(sK1,sK2) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).

fof(f549,plain,
    ( spl4_68
  <=> k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f1529,plain,
    ( k2_xboole_0(sK1,sK2) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl4_34
    | ~ spl4_50
    | ~ spl4_68 ),
    inference(forward_demodulation,[],[f1528,f550])).

fof(f550,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2)
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f549])).

fof(f1528,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f1487,f416])).

fof(f1487,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2))) = k4_xboole_0(sK0,k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)))
    | ~ spl4_34 ),
    inference(resolution,[],[f173,f265])).

fof(f1571,plain,
    ( spl4_158
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f1554,f166,f103,f1569])).

fof(f1569,plain,
    ( spl4_158
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_158])])).

fof(f166,plain,
    ( spl4_16
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f1554,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f1512,f167])).

fof(f167,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f1512,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f173,f104])).

fof(f1564,plain,
    ( spl4_156
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f1553,f159,f96,f1562])).

fof(f1562,plain,
    ( spl4_156
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_156])])).

fof(f159,plain,
    ( spl4_14
  <=> k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1553,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1511,f160])).

fof(f160,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f1511,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k4_xboole_0(sK0,k3_subset_1(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f173,f97])).

fof(f1473,plain,
    ( spl4_154
    | ~ spl4_4
    | ~ spl4_142 ),
    inference(avatar_split_clause,[],[f1381,f1365,f96,f1471])).

fof(f1471,plain,
    ( spl4_154
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).

fof(f1365,plain,
    ( spl4_142
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).

fof(f1381,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_142 ),
    inference(forward_demodulation,[],[f1373,f1372])).

fof(f1372,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))))
    | ~ spl4_4
    | ~ spl4_142 ),
    inference(resolution,[],[f1366,f377])).

fof(f1366,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))),k1_zfmisc_1(sK0))
    | ~ spl4_142 ),
    inference(avatar_component_clause,[],[f1365])).

fof(f1373,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_142 ),
    inference(resolution,[],[f1366,f244])).

fof(f1443,plain,
    ( spl4_152
    | ~ spl4_138 ),
    inference(avatar_split_clause,[],[f1333,f1323,f1441])).

fof(f1441,plain,
    ( spl4_152
  <=> k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).

fof(f1333,plain,
    ( k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))
    | ~ spl4_138 ),
    inference(resolution,[],[f1324,f68])).

fof(f1436,plain,
    ( spl4_150
    | ~ spl4_138 ),
    inference(avatar_split_clause,[],[f1332,f1323,f1434])).

fof(f1332,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))) = k2_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_138 ),
    inference(resolution,[],[f1324,f67])).

fof(f1416,plain,
    ( spl4_148
    | ~ spl4_132 ),
    inference(avatar_split_clause,[],[f1282,f1234,f1414])).

fof(f1414,plain,
    ( spl4_148
  <=> k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))) = k4_xboole_0(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).

fof(f1282,plain,
    ( k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))) = k4_xboole_0(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))
    | ~ spl4_132 ),
    inference(resolution,[],[f1235,f68])).

fof(f1409,plain,
    ( spl4_146
    | ~ spl4_132 ),
    inference(avatar_split_clause,[],[f1281,f1234,f1407])).

fof(f1281,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_132 ),
    inference(resolution,[],[f1235,f67])).

fof(f1388,plain,
    ( spl4_144
    | ~ spl4_4
    | ~ spl4_140 ),
    inference(avatar_split_clause,[],[f1360,f1344,f96,f1386])).

fof(f1344,plain,
    ( spl4_140
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).

fof(f1360,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_140 ),
    inference(forward_demodulation,[],[f1352,f1351])).

fof(f1351,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))))
    | ~ spl4_4
    | ~ spl4_140 ),
    inference(resolution,[],[f1345,f377])).

fof(f1345,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_140 ),
    inference(avatar_component_clause,[],[f1344])).

fof(f1352,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_140 ),
    inference(resolution,[],[f1345,f244])).

fof(f1367,plain,
    ( spl4_142
    | ~ spl4_4
    | ~ spl4_134 ),
    inference(avatar_split_clause,[],[f1309,f1293,f96,f1365])).

fof(f1293,plain,
    ( spl4_134
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f1309,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_134 ),
    inference(forward_demodulation,[],[f1301,f1300])).

fof(f1300,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))))
    | ~ spl4_4
    | ~ spl4_134 ),
    inference(resolution,[],[f1294,f377])).

fof(f1294,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))),k1_zfmisc_1(sK0))
    | ~ spl4_134 ),
    inference(avatar_component_clause,[],[f1293])).

fof(f1301,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_134 ),
    inference(resolution,[],[f1294,f244])).

fof(f1346,plain,
    ( spl4_140
    | ~ spl4_4
    | ~ spl4_138 ),
    inference(avatar_split_clause,[],[f1339,f1323,f96,f1344])).

fof(f1339,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_138 ),
    inference(forward_demodulation,[],[f1331,f1330])).

fof(f1330,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2)))
    | ~ spl4_4
    | ~ spl4_138 ),
    inference(resolution,[],[f1324,f377])).

fof(f1331,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_138 ),
    inference(resolution,[],[f1324,f244])).

fof(f1325,plain,
    ( spl4_138
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_136 ),
    inference(avatar_split_clause,[],[f1318,f1314,f103,f96,f1323])).

fof(f1318,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_136 ),
    inference(subsumption_resolution,[],[f1317,f104])).

fof(f1317,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK2)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_136 ),
    inference(superposition,[],[f257,f1315])).

fof(f1316,plain,
    ( spl4_136
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1207,f103,f96,f1314])).

fof(f1207,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) = k2_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f403,f104])).

fof(f1295,plain,
    ( spl4_134
    | ~ spl4_4
    | ~ spl4_132 ),
    inference(avatar_split_clause,[],[f1288,f1234,f96,f1293])).

fof(f1288,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_132 ),
    inference(forward_demodulation,[],[f1280,f1279])).

fof(f1279,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_132 ),
    inference(resolution,[],[f1235,f377])).

fof(f1280,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k3_subset_1(sK0,sK1))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_132 ),
    inference(resolution,[],[f1235,f244])).

fof(f1236,plain,
    ( spl4_132
    | ~ spl4_4
    | ~ spl4_130 ),
    inference(avatar_split_clause,[],[f1229,f1225,f96,f1234])).

fof(f1229,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_130 ),
    inference(subsumption_resolution,[],[f1228,f97])).

fof(f1228,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k3_subset_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_130 ),
    inference(superposition,[],[f257,f1226])).

fof(f1227,plain,
    ( spl4_130
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1206,f96,f1225])).

fof(f1206,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f403,f97])).

fof(f1130,plain,
    ( spl4_128
    | ~ spl4_4
    | ~ spl4_102 ),
    inference(avatar_split_clause,[],[f900,f886,f96,f1128])).

fof(f1128,plain,
    ( spl4_128
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).

fof(f886,plain,
    ( spl4_102
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f900,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_102 ),
    inference(forward_demodulation,[],[f893,f892])).

fof(f892,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))))
    | ~ spl4_4
    | ~ spl4_102 ),
    inference(resolution,[],[f887,f377])).

fof(f887,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(sK0))
    | ~ spl4_102 ),
    inference(avatar_component_clause,[],[f886])).

fof(f893,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_102 ),
    inference(resolution,[],[f887,f244])).

fof(f1111,plain,
    ( spl4_126
    | ~ spl4_4
    | ~ spl4_88 ),
    inference(avatar_split_clause,[],[f789,f775,f96,f1109])).

fof(f1109,plain,
    ( spl4_126
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).

fof(f775,plain,
    ( spl4_88
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f789,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_88 ),
    inference(forward_demodulation,[],[f782,f781])).

fof(f781,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))))
    | ~ spl4_4
    | ~ spl4_88 ),
    inference(resolution,[],[f776,f377])).

fof(f776,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f775])).

fof(f782,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_88 ),
    inference(resolution,[],[f776,f244])).

fof(f1094,plain,
    ( spl4_124
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f833,f816,f1092])).

fof(f833,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl4_94 ),
    inference(resolution,[],[f817,f67])).

fof(f1087,plain,
    ( spl4_122
    | ~ spl4_94 ),
    inference(avatar_split_clause,[],[f832,f816,f1085])).

fof(f1085,plain,
    ( spl4_122
  <=> k3_subset_1(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).

fof(f832,plain,
    ( k3_subset_1(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))
    | ~ spl4_94 ),
    inference(resolution,[],[f817,f68])).

fof(f1057,plain,
    ( spl4_120
    | ~ spl4_4
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f770,f756,f96,f1055])).

fof(f1055,plain,
    ( spl4_120
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f756,plain,
    ( spl4_86
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f770,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_86 ),
    inference(forward_demodulation,[],[f763,f762])).

fof(f762,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))))
    | ~ spl4_4
    | ~ spl4_86 ),
    inference(resolution,[],[f757,f377])).

fof(f757,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_86 ),
    inference(avatar_component_clause,[],[f756])).

fof(f763,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_86 ),
    inference(resolution,[],[f757,f244])).

fof(f1050,plain,
    ( spl4_118
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f568,f559,f1048])).

fof(f1048,plain,
    ( spl4_118
  <=> k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f559,plain,
    ( spl4_70
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f568,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl4_70 ),
    inference(resolution,[],[f560,f67])).

fof(f560,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f559])).

fof(f1043,plain,
    ( spl4_116
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f567,f559,f1041])).

fof(f1041,plain,
    ( spl4_116
  <=> k3_subset_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f567,plain,
    ( k3_subset_1(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)))
    | ~ spl4_70 ),
    inference(resolution,[],[f560,f68])).

fof(f971,plain,
    ( spl4_114
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_38
    | ~ spl4_46
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f428,f415,f348,f294,f264,f103,f96,f969])).

fof(f969,plain,
    ( spl4_114
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).

fof(f294,plain,
    ( spl4_38
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f348,plain,
    ( spl4_46
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK2))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f428,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_38
    | ~ spl4_46
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f427,f409])).

fof(f409,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f399,f393])).

fof(f393,plain,
    ( k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f377,f104])).

fof(f399,plain,
    ( k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK2)) = k2_xboole_0(sK1,k4_subset_1(sK0,sK1,sK2))
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(resolution,[],[f377,f265])).

fof(f427,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_38
    | ~ spl4_46
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f424,f406])).

fof(f406,plain,
    ( k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK2)))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f394,f393])).

fof(f394,plain,
    ( k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK2))) = k2_xboole_0(sK1,k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK2)))
    | ~ spl4_4
    | ~ spl4_38 ),
    inference(resolution,[],[f377,f295])).

fof(f295,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f294])).

fof(f424,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_46
    | ~ spl4_50 ),
    inference(superposition,[],[f349,f416])).

fof(f349,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f348])).

fof(f958,plain,
    ( spl4_112
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f536,f527,f956])).

fof(f536,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_64 ),
    inference(resolution,[],[f528,f67])).

fof(f951,plain,
    ( spl4_110
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f535,f527,f949])).

fof(f949,plain,
    ( spl4_110
  <=> k3_subset_1(sK0,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).

fof(f535,plain,
    ( k3_subset_1(sK0,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_64 ),
    inference(resolution,[],[f528,f68])).

fof(f933,plain,
    ( spl4_108
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f517,f508,f931])).

fof(f508,plain,
    ( spl4_62
  <=> m1_subset_1(k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f517,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_62 ),
    inference(resolution,[],[f509,f67])).

fof(f509,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f508])).

fof(f926,plain,
    ( spl4_106
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f516,f508,f924])).

fof(f924,plain,
    ( spl4_106
  <=> k3_subset_1(sK0,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f516,plain,
    ( k3_subset_1(sK0,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_62 ),
    inference(resolution,[],[f509,f68])).

fof(f907,plain,
    ( spl4_104
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f653,f415,f264,f103,f96,f905])).

fof(f905,plain,
    ( spl4_104
  <=> k4_subset_1(sK0,k2_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f653,plain,
    ( k4_subset_1(sK0,k2_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f652,f409])).

fof(f652,plain,
    ( k4_subset_1(sK0,k2_xboole_0(sK1,sK2),sK1) = k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK2))
    | ~ spl4_4
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f629,f416])).

fof(f629,plain,
    ( k4_subset_1(sK0,k4_subset_1(sK0,sK1,sK2),sK1) = k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK2))
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(resolution,[],[f584,f265])).

fof(f888,plain,
    ( spl4_102
    | ~ spl4_4
    | ~ spl4_100 ),
    inference(avatar_split_clause,[],[f881,f867,f96,f886])).

fof(f867,plain,
    ( spl4_100
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f881,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_100 ),
    inference(forward_demodulation,[],[f874,f873])).

fof(f873,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))))
    | ~ spl4_4
    | ~ spl4_100 ),
    inference(resolution,[],[f868,f377])).

fof(f868,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_100 ),
    inference(avatar_component_clause,[],[f867])).

fof(f874,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_100 ),
    inference(resolution,[],[f868,f244])).

fof(f869,plain,
    ( spl4_100
    | ~ spl4_4
    | ~ spl4_94
    | ~ spl4_98 ),
    inference(avatar_split_clause,[],[f862,f859,f816,f96,f867])).

fof(f859,plain,
    ( spl4_98
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f862,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_94
    | ~ spl4_98 ),
    inference(forward_demodulation,[],[f860,f827])).

fof(f827,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)))
    | ~ spl4_4
    | ~ spl4_94 ),
    inference(resolution,[],[f817,f377])).

fof(f860,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_98 ),
    inference(avatar_component_clause,[],[f859])).

fof(f861,plain,
    ( spl4_98
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_52
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f810,f805,f433,f103,f96,f859])).

fof(f805,plain,
    ( spl4_92
  <=> k4_subset_1(sK0,sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f810,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_52
    | ~ spl4_92 ),
    inference(subsumption_resolution,[],[f808,f434])).

fof(f808,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_92 ),
    inference(superposition,[],[f284,f806])).

fof(f806,plain,
    ( k4_subset_1(sK0,sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl4_92 ),
    inference(avatar_component_clause,[],[f805])).

fof(f284,plain,
    ( ! [X0] :
        ( m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK2,X0)),k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f245,f244])).

fof(f841,plain,
    ( spl4_96
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f693,f415,f264,f103,f839])).

fof(f839,plain,
    ( spl4_96
  <=> k4_subset_1(sK0,k2_xboole_0(sK1,sK2),sK2) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f693,plain,
    ( k4_subset_1(sK0,k2_xboole_0(sK1,sK2),sK2) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f692,f472])).

fof(f472,plain,
    ( k4_subset_1(sK0,sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f456,f416])).

fof(f456,plain,
    ( k4_subset_1(sK0,sK2,k4_subset_1(sK0,sK1,sK2)) = k2_xboole_0(sK2,k4_subset_1(sK0,sK1,sK2))
    | ~ spl4_6
    | ~ spl4_34 ),
    inference(resolution,[],[f378,f265])).

fof(f692,plain,
    ( k4_subset_1(sK0,k2_xboole_0(sK1,sK2),sK2) = k4_subset_1(sK0,sK2,k2_xboole_0(sK1,sK2))
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f669,f416])).

fof(f669,plain,
    ( k4_subset_1(sK0,k4_subset_1(sK0,sK1,sK2),sK2) = k4_subset_1(sK0,sK2,k4_subset_1(sK0,sK1,sK2))
    | ~ spl4_6
    | ~ spl4_34 ),
    inference(resolution,[],[f585,f265])).

fof(f818,plain,
    ( spl4_94
    | ~ spl4_6
    | ~ spl4_52
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f811,f805,f433,f103,f816])).

fof(f811,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_6
    | ~ spl4_52
    | ~ spl4_92 ),
    inference(subsumption_resolution,[],[f809,f434])).

fof(f809,plain,
    ( m1_subset_1(k2_xboole_0(sK2,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_6
    | ~ spl4_92 ),
    inference(superposition,[],[f245,f806])).

fof(f807,plain,
    ( spl4_92
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f472,f415,f264,f103,f805])).

fof(f800,plain,
    ( spl4_90
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f409,f264,f103,f96,f798])).

fof(f798,plain,
    ( spl4_90
  <=> k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f777,plain,
    ( spl4_88
    | ~ spl4_4
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f623,f611,f96,f775])).

fof(f611,plain,
    ( spl4_74
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f623,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_74 ),
    inference(forward_demodulation,[],[f616,f615])).

fof(f615,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))))
    | ~ spl4_4
    | ~ spl4_74 ),
    inference(resolution,[],[f612,f377])).

fof(f612,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f611])).

fof(f616,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_74 ),
    inference(resolution,[],[f612,f244])).

fof(f758,plain,
    ( spl4_86
    | ~ spl4_4
    | ~ spl4_82 ),
    inference(avatar_split_clause,[],[f744,f730,f96,f756])).

fof(f730,plain,
    ( spl4_82
  <=> m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f744,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_82 ),
    inference(forward_demodulation,[],[f737,f736])).

fof(f736,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))) = k2_xboole_0(sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))))
    | ~ spl4_4
    | ~ spl4_82 ),
    inference(resolution,[],[f731,f377])).

fof(f731,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f730])).

fof(f737,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_82 ),
    inference(resolution,[],[f731,f244])).

fof(f751,plain,
    ( spl4_84
    | ~ spl4_48
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f425,f415,f373,f749])).

fof(f749,plain,
    ( spl4_84
  <=> k4_subset_1(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f373,plain,
    ( spl4_48
  <=> k4_subset_1(sK0,sK1,sK2) = k4_subset_1(sK0,k4_subset_1(sK0,sK1,sK2),k4_subset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f425,plain,
    ( k4_subset_1(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,sK2)
    | ~ spl4_48
    | ~ spl4_50 ),
    inference(superposition,[],[f374,f416])).

fof(f374,plain,
    ( k4_subset_1(sK0,sK1,sK2) = k4_subset_1(sK0,k4_subset_1(sK0,sK1,sK2),k4_subset_1(sK0,sK1,sK2))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f373])).

fof(f732,plain,
    ( spl4_82
    | ~ spl4_4
    | ~ spl4_64
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f725,f722,f527,f96,f730])).

fof(f722,plain,
    ( spl4_80
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f725,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_64
    | ~ spl4_80 ),
    inference(forward_demodulation,[],[f723,f531])).

fof(f531,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))) = k2_xboole_0(sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_4
    | ~ spl4_64 ),
    inference(resolution,[],[f528,f377])).

fof(f723,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f722])).

fof(f724,plain,
    ( spl4_80
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f521,f499,f103,f96,f722])).

fof(f499,plain,
    ( spl4_60
  <=> k4_subset_1(sK0,sK2,sK3(k1_zfmisc_1(sK0))) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f521,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(subsumption_resolution,[],[f519,f62])).

fof(f519,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(superposition,[],[f284,f500])).

fof(f500,plain,
    ( k4_subset_1(sK0,sK2,sK3(k1_zfmisc_1(sK0))) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f499])).

fof(f717,plain,
    ( spl4_78
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f703,f499,f103,f715])).

fof(f715,plain,
    ( spl4_78
  <=> k4_subset_1(sK0,sK3(k1_zfmisc_1(sK0)),sK2) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f703,plain,
    ( k4_subset_1(sK0,sK3(k1_zfmisc_1(sK0)),sK2) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(forward_demodulation,[],[f681,f500])).

fof(f681,plain,
    ( k4_subset_1(sK0,sK2,sK3(k1_zfmisc_1(sK0))) = k4_subset_1(sK0,sK3(k1_zfmisc_1(sK0)),sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f585,f62])).

fof(f710,plain,
    ( spl4_76
    | ~ spl4_4
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f663,f492,f96,f708])).

fof(f708,plain,
    ( spl4_76
  <=> k4_subset_1(sK0,sK3(k1_zfmisc_1(sK0)),sK1) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f663,plain,
    ( k4_subset_1(sK0,sK3(k1_zfmisc_1(sK0)),sK1) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_4
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f641,f493])).

fof(f641,plain,
    ( k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))) = k4_subset_1(sK0,sK3(k1_zfmisc_1(sK0)),sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f584,f62])).

fof(f613,plain,
    ( spl4_74
    | ~ spl4_4
    | ~ spl4_62
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f606,f603,f508,f96,f611])).

fof(f603,plain,
    ( spl4_72
  <=> m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f606,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_62
    | ~ spl4_72 ),
    inference(forward_demodulation,[],[f604,f512])).

fof(f512,plain,
    ( k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))) = k2_xboole_0(sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))))
    | ~ spl4_4
    | ~ spl4_62 ),
    inference(resolution,[],[f509,f377])).

fof(f604,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f603])).

fof(f605,plain,
    ( spl4_72
    | ~ spl4_44
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f502,f492,f329,f603])).

fof(f502,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_44
    | ~ spl4_58 ),
    inference(superposition,[],[f330,f493])).

fof(f561,plain,
    ( spl4_70
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_38
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f426,f415,f294,f264,f103,f96,f559])).

fof(f426,plain,
    ( m1_subset_1(k2_xboole_0(sK1,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_34
    | ~ spl4_38
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f421,f409])).

fof(f421,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_38
    | ~ spl4_50 ),
    inference(superposition,[],[f295,f416])).

fof(f551,plain,
    ( spl4_68
    | ~ spl4_42
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f423,f415,f322,f549])).

fof(f322,plain,
    ( spl4_42
  <=> k4_subset_1(sK0,sK1,sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f423,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2)
    | ~ spl4_42
    | ~ spl4_50 ),
    inference(superposition,[],[f323,f416])).

fof(f323,plain,
    ( k4_subset_1(sK0,sK1,sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f322])).

fof(f544,plain,
    ( spl4_66
    | ~ spl4_40
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f422,f415,f315,f542])).

fof(f542,plain,
    ( spl4_66
  <=> k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f315,plain,
    ( spl4_40
  <=> k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)) = k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f422,plain,
    ( k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_40
    | ~ spl4_50 ),
    inference(superposition,[],[f316,f416])).

fof(f316,plain,
    ( k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)) = k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f315])).

fof(f529,plain,
    ( spl4_64
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f522,f499,f103,f527])).

fof(f522,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0))
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(subsumption_resolution,[],[f520,f62])).

fof(f520,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(sK0)),k1_zfmisc_1(sK0))
    | ~ spl4_6
    | ~ spl4_60 ),
    inference(superposition,[],[f245,f500])).

fof(f510,plain,
    ( spl4_62
    | ~ spl4_36
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f503,f492,f276,f508])).

fof(f503,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0))
    | ~ spl4_36
    | ~ spl4_58 ),
    inference(superposition,[],[f277,f493])).

fof(f501,plain,
    ( spl4_60
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f464,f103,f499])).

fof(f464,plain,
    ( k4_subset_1(sK0,sK2,sK3(k1_zfmisc_1(sK0))) = k2_xboole_0(sK2,sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_6 ),
    inference(resolution,[],[f378,f62])).

fof(f494,plain,
    ( spl4_58
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f404,f96,f492])).

fof(f404,plain,
    ( k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))) = k2_xboole_0(sK1,sK3(k1_zfmisc_1(sK0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f377,f62])).

fof(f483,plain,
    ( spl4_56
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f475,f103,f96,f481])).

fof(f481,plain,
    ( spl4_56
  <=> k4_subset_1(sK0,sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f475,plain,
    ( k4_subset_1(sK0,sK2,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f461,f65])).

fof(f461,plain,
    ( k4_subset_1(sK0,sK2,sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f378,f97])).

fof(f450,plain,
    ( ~ spl4_55
    | spl4_9
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f418,f415,f130,f448])).

fof(f130,plain,
    ( spl4_9
  <=> ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f418,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ spl4_9
    | ~ spl4_50 ),
    inference(superposition,[],[f131,f416])).

fof(f131,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f435,plain,
    ( spl4_52
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f419,f415,f264,f433])).

fof(f419,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_34
    | ~ spl4_50 ),
    inference(superposition,[],[f265,f416])).

fof(f417,plain,
    ( spl4_50
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f393,f103,f96,f415])).

fof(f375,plain,
    ( spl4_48
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f271,f264,f373])).

fof(f271,plain,
    ( k4_subset_1(sK0,sK1,sK2) = k4_subset_1(sK0,k4_subset_1(sK0,sK1,sK2),k4_subset_1(sK0,sK1,sK2))
    | ~ spl4_34 ),
    inference(resolution,[],[f265,f76])).

fof(f350,plain,
    ( spl4_46
    | ~ spl4_4
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f297,f294,f96,f348])).

fof(f297,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK2))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_38 ),
    inference(resolution,[],[f295,f244])).

fof(f331,plain,
    ( spl4_44
    | ~ spl4_4
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f279,f276,f96,f329])).

fof(f279,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0)))),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_36 ),
    inference(resolution,[],[f277,f244])).

fof(f324,plain,
    ( spl4_42
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f270,f264,f322])).

fof(f270,plain,
    ( k4_subset_1(sK0,sK1,sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)))
    | ~ spl4_34 ),
    inference(resolution,[],[f265,f67])).

fof(f317,plain,
    ( spl4_40
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f269,f264,f315])).

fof(f269,plain,
    ( k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)) = k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2))
    | ~ spl4_34 ),
    inference(resolution,[],[f265,f68])).

fof(f296,plain,
    ( spl4_38
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f267,f264,f96,f294])).

fof(f267,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,k4_subset_1(sK0,sK1,sK2)),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_34 ),
    inference(resolution,[],[f265,f244])).

fof(f278,plain,
    ( spl4_36
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f258,f96,f276])).

fof(f258,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,sK3(k1_zfmisc_1(sK0))),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f244,f62])).

fof(f266,plain,
    ( spl4_34
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f256,f103,f96,f264])).

fof(f256,plain,
    ( m1_subset_1(k4_subset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f244,f104])).

fof(f243,plain,
    ( spl4_32
    | ~ spl4_26
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f236,f233,f218,f241])).

fof(f241,plain,
    ( spl4_32
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f218,plain,
    ( spl4_26
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f233,plain,
    ( spl4_30
  <=> k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f236,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_26
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f234,f219])).

fof(f219,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f218])).

fof(f234,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f233])).

fof(f235,plain,
    ( spl4_30
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f199,f196,f233])).

fof(f196,plain,
    ( spl4_22
  <=> k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f199,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(superposition,[],[f147,f197])).

fof(f197,plain,
    ( k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f196])).

fof(f147,plain,(
    ! [X2] : k3_subset_1(X2,k3_subset_1(X2,sK3(k1_zfmisc_1(X2)))) = sK3(k1_zfmisc_1(X2)) ),
    inference(resolution,[],[f67,f62])).

fof(f228,plain,
    ( spl4_28
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f211,f206,f226])).

fof(f226,plain,
    ( spl4_28
  <=> k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f206,plain,
    ( spl4_24
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f211,plain,
    ( k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_24 ),
    inference(resolution,[],[f207,f76])).

fof(f207,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f206])).

fof(f220,plain,
    ( spl4_26
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f212,f206,f218])).

fof(f212,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f209,f58])).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',t3_boole)).

fof(f209,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_24 ),
    inference(resolution,[],[f207,f68])).

fof(f208,plain,
    ( spl4_24
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f201,f196,f206])).

fof(f201,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f200,f62])).

fof(f200,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK3(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_22 ),
    inference(superposition,[],[f66,f197])).

fof(f198,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f190,f196])).

fof(f190,plain,(
    k3_subset_1(k1_xboole_0,sK3(k1_zfmisc_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[],[f174,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',t4_boole)).

fof(f174,plain,(
    ! [X2] : k3_subset_1(X2,sK3(k1_zfmisc_1(X2))) = k4_xboole_0(X2,sK3(k1_zfmisc_1(X2))) ),
    inference(resolution,[],[f68,f62])).

fof(f188,plain,
    ( spl4_20
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f172,f103,f186])).

fof(f186,plain,
    ( spl4_20
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f172,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f68,f104])).

fof(f181,plain,
    ( spl4_18
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f171,f96,f179])).

fof(f179,plain,
    ( spl4_18
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f171,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f68,f97])).

fof(f168,plain,
    ( spl4_16
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f145,f103,f166])).

fof(f145,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = sK2
    | ~ spl4_6 ),
    inference(resolution,[],[f67,f104])).

fof(f161,plain,
    ( spl4_14
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f144,f96,f159])).

fof(f144,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f67,f97])).

fof(f154,plain,
    ( spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f134,f103,f152])).

fof(f152,plain,
    ( spl4_12
  <=> k4_subset_1(sK0,sK2,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f134,plain,
    ( k4_subset_1(sK0,sK2,sK2) = sK2
    | ~ spl4_6 ),
    inference(resolution,[],[f76,f104])).

fof(f143,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f133,f96,f141])).

fof(f141,plain,
    ( spl4_10
  <=> k4_subset_1(sK0,sK1,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f133,plain,
    ( k4_subset_1(sK0,sK1,sK1) = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f76,f97])).

fof(f132,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f55,f130])).

fof(f55,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f48,f47])).

fof(f47,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,X2)),k3_subset_1(sK0,sK1))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,sK2)),k3_subset_1(X0,X1))
        & m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',t41_subset_1)).

fof(f105,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f54,f103])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f53,f96])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f91,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f57,f89])).

fof(f89,plain,
    ( spl4_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f57,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',d2_xboole_0)).

fof(f84,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f77,f82])).

fof(f82,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f77,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f56,f57])).

fof(f56,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t41_subset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
