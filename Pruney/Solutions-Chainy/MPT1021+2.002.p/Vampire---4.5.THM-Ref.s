%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:49 EST 2020

% Result     : Theorem 3.71s
% Output     : Refutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  203 (1573 expanded)
%              Number of leaves         :   34 ( 416 expanded)
%              Depth                    :   20
%              Number of atoms          :  611 (7948 expanded)
%              Number of equality atoms :  147 ( 332 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1838,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f235,f399,f443,f469,f475,f483,f1825])).

fof(f1825,plain,
    ( ~ spl6_3
    | spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f1824])).

fof(f1824,plain,
    ( $false
    | ~ spl6_3
    | spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f1796,f631])).

fof(f631,plain,
    ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) != k6_partfun1(k1_xboole_0)
    | ~ spl6_3
    | spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f576,f340])).

fof(f340,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f576,plain,
    ( k6_partfun1(sK0) != k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f343,f398])).

fof(f398,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f343,plain,
    ( k6_partfun1(sK0) != k5_relat_1(sK1,k2_funct_1(sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl6_4
  <=> k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1796,plain,
    ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f509,f1764])).

fof(f1764,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f130,f1494,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f1494,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f1440,f1446])).

fof(f1446,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f130,f1334,f178])).

fof(f1334,plain,
    ( v1_xboole_0(k3_relat_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f1319,f637])).

fof(f637,plain,
    ( k1_xboole_0 = k2_wellord1(k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f557,f340])).

fof(f557,plain,
    ( k1_xboole_0 = k2_wellord1(k1_xboole_0,sK0)
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f438,f398])).

fof(f438,plain,(
    sK1 = k2_wellord1(sK1,sK0) ),
    inference(forward_demodulation,[],[f437,f287])).

fof(f287,plain,(
    sK1 = k8_relat_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f276,f284])).

fof(f284,plain,(
    sK0 = k2_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f241,f243,f249,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f249,plain,(
    v2_funct_2(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f125,f127,f128,f199])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f128,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f106])).

fof(f106,plain,
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

fof(f53,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f48])).

fof(f48,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f127,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f107])).

fof(f125,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f107])).

fof(f243,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f128,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f241,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f128,f184])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f276,plain,(
    sK1 = k8_relat_1(k2_relat_1(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f216,f241,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f216,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f437,plain,(
    k8_relat_1(sK0,sK1) = k2_wellord1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f435,f241])).

fof(f435,plain,
    ( k8_relat_1(sK0,sK1) = k2_wellord1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f154,f282])).

fof(f282,plain,(
    sK1 = k7_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f241,f242,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f242,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f128,f185])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f154,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

fof(f1319,plain,
    ( v1_xboole_0(k3_relat_1(k2_wellord1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f131,f508,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f508,plain,
    ( ! [X0] : r1_tarski(k3_relat_1(k2_wellord1(k1_xboole_0,X0)),X0)
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f274,f398])).

fof(f274,plain,(
    ! [X0] : r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f241,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

fof(f131,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f1440,plain,
    ( v1_xboole_0(k1_relat_1(k3_relat_1(k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f1334,f143])).

fof(f143,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f130,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f509,plain,
    ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_relat_1(k1_xboole_0))
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f279,f398])).

fof(f279,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f241,f125,f248,f214])).

fof(f214,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f148,f132])).

fof(f132,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f148,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f248,plain,(
    v2_funct_1(sK1) ),
    inference(unit_resulting_resolution,[],[f125,f127,f128,f198])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f483,plain,
    ( spl6_3
    | spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f482,f346,f342,f338])).

fof(f346,plain,
    ( spl6_5
  <=> sK0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f482,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f481,f125])).

fof(f481,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f480,f126])).

fof(f126,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f107])).

fof(f480,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f479,f128])).

fof(f479,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f464,f248])).

fof(f464,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_5 ),
    inference(trivial_inequality_removal,[],[f461])).

fof(f461,plain,
    ( sK0 != sK0
    | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl6_5 ),
    inference(superposition,[],[f200,f445])).

fof(f445,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f259,f347])).

fof(f347,plain,
    ( sK0 = k9_relat_1(sK1,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f346])).

fof(f259,plain,(
    k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f244,f250])).

fof(f250,plain,(
    ! [X0] : k7_relset_1(sK0,sK0,sK1,X0) = k9_relat_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f128,f203])).

fof(f203,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f244,plain,(
    k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f128,f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f475,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f473,f471])).

fof(f471,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl6_2 ),
    inference(forward_demodulation,[],[f470,f322])).

fof(f322,plain,(
    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(forward_demodulation,[],[f313,f286])).

fof(f286,plain,(
    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    inference(backward_demodulation,[],[f280,f284])).

fof(f280,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f241,f125,f248,f213])).

fof(f213,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f149,f132])).

fof(f149,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f313,plain,(
    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f125,f265,f128,f262,f206])).

fof(f206,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f104])).

fof(f104,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f262,plain,(
    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f239,f240])).

fof(f240,plain,(
    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(unit_resulting_resolution,[],[f125,f126,f127,f128,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f239,plain,(
    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f125,f126,f127,f128,f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f265,plain,(
    v1_funct_1(k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f236,f240])).

fof(f236,plain,(
    v1_funct_1(k2_funct_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f125,f126,f127,f128,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f470,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl6_2 ),
    inference(forward_demodulation,[],[f234,f240])).

fof(f234,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl6_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f473,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl6_1
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f472,f447])).

fof(f447,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f320,f446])).

fof(f446,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK1))
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f279,f344])).

fof(f344,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f342])).

fof(f320,plain,(
    k6_partfun1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(forward_demodulation,[],[f316,f279])).

fof(f316,plain,(
    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f125,f128,f265,f262,f206])).

fof(f472,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f229,f240])).

fof(f229,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl6_1
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f469,plain,
    ( spl6_1
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | spl6_1
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f465,f137])).

fof(f137,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f465,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f448,f226])).

fof(f226,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f205])).

fof(f205,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f448,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl6_1
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f281,f446])).

fof(f281,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0))
    | spl6_1 ),
    inference(backward_demodulation,[],[f270,f279])).

fof(f270,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl6_1 ),
    inference(subsumption_resolution,[],[f269,f125])).

fof(f269,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ v1_funct_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f268,f128])).

fof(f268,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f267,f265])).

fof(f267,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f266,f262])).

fof(f266,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl6_1 ),
    inference(superposition,[],[f261,f206])).

fof(f261,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl6_1 ),
    inference(backward_demodulation,[],[f230,f240])).

fof(f230,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f228])).

fof(f443,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f440,f346])).

fof(f440,plain,(
    sK0 = k9_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f439,f284])).

fof(f439,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f436,f241])).

fof(f436,plain,
    ( k2_relat_1(sK1) = k9_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f153,f282])).

fof(f153,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f399,plain,
    ( spl6_6
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f394,f338,f396])).

fof(f394,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f384,f241])).

fof(f384,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f141,f284])).

fof(f141,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f235,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f129,f232,f228])).

fof(f129,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:26:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (18786)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.55  % (18806)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.26/0.55  % (18808)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.26/0.55  % (18813)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.26/0.55  % (18800)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.55  % (18789)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.26/0.55  % (18790)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.55  % (18785)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.26/0.55  % (18796)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.56  % (18793)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.56  % (18794)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.56  % (18792)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.43/0.56  % (18804)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.56  % (18805)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.56  % (18799)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.56  % (18811)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.56  % (18814)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.56  % (18809)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.56  % (18791)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.43/0.57  % (18797)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.57  % (18801)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.57  % (18798)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.57  % (18803)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.57  % (18812)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.57  % (18788)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.43/0.57  % (18807)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.58  % (18810)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.58  % (18795)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.59  % (18787)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.43/0.61  % (18802)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 3.42/0.83  % (18790)Time limit reached!
% 3.42/0.83  % (18790)------------------------------
% 3.42/0.83  % (18790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.83  % (18790)Termination reason: Time limit
% 3.42/0.83  
% 3.42/0.83  % (18790)Memory used [KB]: 8059
% 3.42/0.83  % (18790)Time elapsed: 0.414 s
% 3.42/0.83  % (18790)------------------------------
% 3.42/0.83  % (18790)------------------------------
% 3.71/0.89  % (18811)Refutation found. Thanks to Tanya!
% 3.71/0.89  % SZS status Theorem for theBenchmark
% 3.71/0.89  % SZS output start Proof for theBenchmark
% 3.71/0.89  fof(f1838,plain,(
% 3.71/0.89    $false),
% 3.71/0.89    inference(avatar_sat_refutation,[],[f235,f399,f443,f469,f475,f483,f1825])).
% 3.71/0.89  fof(f1825,plain,(
% 3.71/0.89    ~spl6_3 | spl6_4 | ~spl6_6),
% 3.71/0.89    inference(avatar_contradiction_clause,[],[f1824])).
% 3.71/0.89  fof(f1824,plain,(
% 3.71/0.89    $false | (~spl6_3 | spl6_4 | ~spl6_6)),
% 3.71/0.89    inference(subsumption_resolution,[],[f1796,f631])).
% 3.71/0.89  fof(f631,plain,(
% 3.71/0.89    k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) != k6_partfun1(k1_xboole_0) | (~spl6_3 | spl6_4 | ~spl6_6)),
% 3.71/0.89    inference(forward_demodulation,[],[f576,f340])).
% 3.71/0.89  fof(f340,plain,(
% 3.71/0.89    k1_xboole_0 = sK0 | ~spl6_3),
% 3.71/0.89    inference(avatar_component_clause,[],[f338])).
% 3.71/0.89  fof(f338,plain,(
% 3.71/0.89    spl6_3 <=> k1_xboole_0 = sK0),
% 3.71/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.71/0.89  fof(f576,plain,(
% 3.71/0.89    k6_partfun1(sK0) != k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) | (spl6_4 | ~spl6_6)),
% 3.71/0.89    inference(forward_demodulation,[],[f343,f398])).
% 3.71/0.89  fof(f398,plain,(
% 3.71/0.89    k1_xboole_0 = sK1 | ~spl6_6),
% 3.71/0.89    inference(avatar_component_clause,[],[f396])).
% 3.71/0.89  fof(f396,plain,(
% 3.71/0.89    spl6_6 <=> k1_xboole_0 = sK1),
% 3.71/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 3.71/0.89  fof(f343,plain,(
% 3.71/0.89    k6_partfun1(sK0) != k5_relat_1(sK1,k2_funct_1(sK1)) | spl6_4),
% 3.71/0.89    inference(avatar_component_clause,[],[f342])).
% 3.71/0.89  fof(f342,plain,(
% 3.71/0.89    spl6_4 <=> k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 3.71/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 3.71/0.89  fof(f1796,plain,(
% 3.71/0.89    k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_xboole_0) | (~spl6_3 | ~spl6_6)),
% 3.71/0.89    inference(backward_demodulation,[],[f509,f1764])).
% 3.71/0.89  fof(f1764,plain,(
% 3.71/0.89    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl6_3 | ~spl6_6)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f130,f1494,f178])).
% 3.71/0.89  fof(f178,plain,(
% 3.71/0.89    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f86])).
% 3.71/0.89  fof(f86,plain,(
% 3.71/0.89    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.71/0.89    inference(ennf_transformation,[],[f11])).
% 3.71/0.89  fof(f11,axiom,(
% 3.71/0.89    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 3.71/0.89  fof(f1494,plain,(
% 3.71/0.89    v1_xboole_0(k1_relat_1(k1_xboole_0)) | (~spl6_3 | ~spl6_6)),
% 3.71/0.89    inference(forward_demodulation,[],[f1440,f1446])).
% 3.71/0.89  fof(f1446,plain,(
% 3.71/0.89    k1_xboole_0 = k3_relat_1(k1_xboole_0) | (~spl6_3 | ~spl6_6)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f130,f1334,f178])).
% 3.71/0.89  fof(f1334,plain,(
% 3.71/0.89    v1_xboole_0(k3_relat_1(k1_xboole_0)) | (~spl6_3 | ~spl6_6)),
% 3.71/0.89    inference(forward_demodulation,[],[f1319,f637])).
% 3.71/0.89  fof(f637,plain,(
% 3.71/0.89    k1_xboole_0 = k2_wellord1(k1_xboole_0,k1_xboole_0) | (~spl6_3 | ~spl6_6)),
% 3.71/0.89    inference(forward_demodulation,[],[f557,f340])).
% 3.71/0.89  fof(f557,plain,(
% 3.71/0.89    k1_xboole_0 = k2_wellord1(k1_xboole_0,sK0) | ~spl6_6),
% 3.71/0.89    inference(backward_demodulation,[],[f438,f398])).
% 3.71/0.89  fof(f438,plain,(
% 3.71/0.89    sK1 = k2_wellord1(sK1,sK0)),
% 3.71/0.89    inference(forward_demodulation,[],[f437,f287])).
% 3.71/0.89  fof(f287,plain,(
% 3.71/0.89    sK1 = k8_relat_1(sK0,sK1)),
% 3.71/0.89    inference(backward_demodulation,[],[f276,f284])).
% 3.71/0.89  fof(f284,plain,(
% 3.71/0.89    sK0 = k2_relat_1(sK1)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f241,f243,f249,f162])).
% 3.71/0.89  fof(f162,plain,(
% 3.71/0.89    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f113])).
% 3.71/0.89  fof(f113,plain,(
% 3.71/0.89    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.71/0.89    inference(nnf_transformation,[],[f78])).
% 3.71/0.89  fof(f78,plain,(
% 3.71/0.89    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.71/0.89    inference(flattening,[],[f77])).
% 3.71/0.89  fof(f77,plain,(
% 3.71/0.89    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.71/0.89    inference(ennf_transformation,[],[f41])).
% 3.71/0.89  fof(f41,axiom,(
% 3.71/0.89    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 3.71/0.89  fof(f249,plain,(
% 3.71/0.89    v2_funct_2(sK1,sK0)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f125,f127,f128,f199])).
% 3.71/0.89  fof(f199,plain,(
% 3.71/0.89    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.89    inference(cnf_transformation,[],[f97])).
% 3.71/0.89  fof(f97,plain,(
% 3.71/0.89    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.89    inference(flattening,[],[f96])).
% 3.71/0.89  fof(f96,plain,(
% 3.71/0.89    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.89    inference(ennf_transformation,[],[f39])).
% 3.71/0.89  fof(f39,axiom,(
% 3.71/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 3.71/0.89  fof(f128,plain,(
% 3.71/0.89    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.71/0.89    inference(cnf_transformation,[],[f107])).
% 3.71/0.89  fof(f107,plain,(
% 3.71/0.89    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.71/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f106])).
% 3.71/0.89  fof(f106,plain,(
% 3.71/0.89    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.71/0.89    introduced(choice_axiom,[])).
% 3.71/0.89  fof(f53,plain,(
% 3.71/0.89    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.71/0.89    inference(flattening,[],[f52])).
% 3.71/0.89  fof(f52,plain,(
% 3.71/0.89    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.71/0.89    inference(ennf_transformation,[],[f49])).
% 3.71/0.89  fof(f49,negated_conjecture,(
% 3.71/0.89    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.71/0.89    inference(negated_conjecture,[],[f48])).
% 3.71/0.89  fof(f48,conjecture,(
% 3.71/0.89    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 3.71/0.89  fof(f127,plain,(
% 3.71/0.89    v3_funct_2(sK1,sK0,sK0)),
% 3.71/0.89    inference(cnf_transformation,[],[f107])).
% 3.71/0.89  fof(f125,plain,(
% 3.71/0.89    v1_funct_1(sK1)),
% 3.71/0.89    inference(cnf_transformation,[],[f107])).
% 3.71/0.89  fof(f243,plain,(
% 3.71/0.89    v5_relat_1(sK1,sK0)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f128,f186])).
% 3.71/0.89  fof(f186,plain,(
% 3.71/0.89    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.89    inference(cnf_transformation,[],[f91])).
% 3.71/0.89  fof(f91,plain,(
% 3.71/0.89    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.89    inference(ennf_transformation,[],[f33])).
% 3.71/0.89  fof(f33,axiom,(
% 3.71/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.71/0.89  fof(f241,plain,(
% 3.71/0.89    v1_relat_1(sK1)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f128,f184])).
% 3.71/0.89  fof(f184,plain,(
% 3.71/0.89    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.89    inference(cnf_transformation,[],[f90])).
% 3.71/0.89  fof(f90,plain,(
% 3.71/0.89    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.89    inference(ennf_transformation,[],[f32])).
% 3.71/0.89  fof(f32,axiom,(
% 3.71/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.71/0.89  fof(f276,plain,(
% 3.71/0.89    sK1 = k8_relat_1(k2_relat_1(sK1),sK1)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f216,f241,f157])).
% 3.71/0.89  fof(f157,plain,(
% 3.71/0.89    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f72])).
% 3.71/0.89  fof(f72,plain,(
% 3.71/0.89    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.71/0.89    inference(flattening,[],[f71])).
% 3.71/0.89  fof(f71,plain,(
% 3.71/0.89    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.71/0.89    inference(ennf_transformation,[],[f22])).
% 3.71/0.89  fof(f22,axiom,(
% 3.71/0.89    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 3.71/0.89  fof(f216,plain,(
% 3.71/0.89    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.71/0.89    inference(equality_resolution,[],[f170])).
% 3.71/0.89  fof(f170,plain,(
% 3.71/0.89    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.71/0.89    inference(cnf_transformation,[],[f115])).
% 3.71/0.89  fof(f115,plain,(
% 3.71/0.89    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/0.89    inference(flattening,[],[f114])).
% 3.71/0.89  fof(f114,plain,(
% 3.71/0.89    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.71/0.89    inference(nnf_transformation,[],[f7])).
% 3.71/0.89  fof(f7,axiom,(
% 3.71/0.89    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.71/0.89  fof(f437,plain,(
% 3.71/0.89    k8_relat_1(sK0,sK1) = k2_wellord1(sK1,sK0)),
% 3.71/0.89    inference(subsumption_resolution,[],[f435,f241])).
% 3.71/0.89  fof(f435,plain,(
% 3.71/0.89    k8_relat_1(sK0,sK1) = k2_wellord1(sK1,sK0) | ~v1_relat_1(sK1)),
% 3.71/0.89    inference(superposition,[],[f154,f282])).
% 3.71/0.89  fof(f282,plain,(
% 3.71/0.89    sK1 = k7_relat_1(sK1,sK0)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f241,f242,f161])).
% 3.71/0.89  fof(f161,plain,(
% 3.71/0.89    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f76])).
% 3.71/0.89  fof(f76,plain,(
% 3.71/0.89    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.71/0.89    inference(flattening,[],[f75])).
% 3.71/0.89  fof(f75,plain,(
% 3.71/0.89    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.71/0.89    inference(ennf_transformation,[],[f24])).
% 3.71/0.89  fof(f24,axiom,(
% 3.71/0.89    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 3.71/0.89  fof(f242,plain,(
% 3.71/0.89    v4_relat_1(sK1,sK0)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f128,f185])).
% 3.71/0.89  fof(f185,plain,(
% 3.71/0.89    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.89    inference(cnf_transformation,[],[f91])).
% 3.71/0.89  fof(f154,plain,(
% 3.71/0.89    ( ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f69])).
% 3.71/0.89  fof(f69,plain,(
% 3.71/0.89    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.71/0.89    inference(ennf_transformation,[],[f30])).
% 3.71/0.89  fof(f30,axiom,(
% 3.71/0.89    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).
% 3.71/0.89  fof(f1319,plain,(
% 3.71/0.89    v1_xboole_0(k3_relat_1(k2_wellord1(k1_xboole_0,k1_xboole_0))) | ~spl6_6),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f131,f508,f152])).
% 3.71/0.89  fof(f152,plain,(
% 3.71/0.89    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f67])).
% 3.71/0.89  fof(f67,plain,(
% 3.71/0.89    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.71/0.89    inference(flattening,[],[f66])).
% 3.71/0.89  fof(f66,plain,(
% 3.71/0.89    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.71/0.89    inference(ennf_transformation,[],[f9])).
% 3.71/0.89  fof(f9,axiom,(
% 3.71/0.89    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 3.71/0.89  fof(f508,plain,(
% 3.71/0.89    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(k1_xboole_0,X0)),X0)) ) | ~spl6_6),
% 3.71/0.89    inference(backward_demodulation,[],[f274,f398])).
% 3.71/0.89  fof(f274,plain,(
% 3.71/0.89    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0)) )),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f241,f156])).
% 3.71/0.89  fof(f156,plain,(
% 3.71/0.89    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f70])).
% 3.71/0.89  fof(f70,plain,(
% 3.71/0.89    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.71/0.89    inference(ennf_transformation,[],[f31])).
% 3.71/0.89  fof(f31,axiom,(
% 3.71/0.89    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).
% 3.71/0.89  fof(f131,plain,(
% 3.71/0.89    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f8])).
% 3.71/0.89  fof(f8,axiom,(
% 3.71/0.89    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 3.71/0.89  fof(f1440,plain,(
% 3.71/0.89    v1_xboole_0(k1_relat_1(k3_relat_1(k1_xboole_0))) | (~spl6_3 | ~spl6_6)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f1334,f143])).
% 3.71/0.89  fof(f143,plain,(
% 3.71/0.89    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f57])).
% 3.71/0.89  fof(f57,plain,(
% 3.71/0.89    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.71/0.89    inference(ennf_transformation,[],[f18])).
% 3.71/0.89  fof(f18,axiom,(
% 3.71/0.89    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 3.71/0.89  fof(f130,plain,(
% 3.71/0.89    v1_xboole_0(k1_xboole_0)),
% 3.71/0.89    inference(cnf_transformation,[],[f4])).
% 3.71/0.89  fof(f4,axiom,(
% 3.71/0.89    v1_xboole_0(k1_xboole_0)),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.71/0.89  fof(f509,plain,(
% 3.71/0.89    k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_relat_1(k1_xboole_0)) | ~spl6_6),
% 3.71/0.89    inference(backward_demodulation,[],[f279,f398])).
% 3.71/0.89  fof(f279,plain,(
% 3.71/0.89    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f241,f125,f248,f214])).
% 3.71/0.89  fof(f214,plain,(
% 3.71/0.89    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.89    inference(definition_unfolding,[],[f148,f132])).
% 3.71/0.89  fof(f132,plain,(
% 3.71/0.89    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f46])).
% 3.71/0.89  fof(f46,axiom,(
% 3.71/0.89    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 3.71/0.89  fof(f148,plain,(
% 3.71/0.89    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f65])).
% 3.71/0.89  fof(f65,plain,(
% 3.71/0.89    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.71/0.89    inference(flattening,[],[f64])).
% 3.71/0.89  fof(f64,plain,(
% 3.71/0.89    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.71/0.89    inference(ennf_transformation,[],[f28])).
% 3.71/0.89  fof(f28,axiom,(
% 3.71/0.89    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 3.71/0.89  fof(f248,plain,(
% 3.71/0.89    v2_funct_1(sK1)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f125,f127,f128,f198])).
% 3.71/0.89  fof(f198,plain,(
% 3.71/0.89    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.89    inference(cnf_transformation,[],[f97])).
% 3.71/0.89  fof(f483,plain,(
% 3.71/0.89    spl6_3 | spl6_4 | ~spl6_5),
% 3.71/0.89    inference(avatar_split_clause,[],[f482,f346,f342,f338])).
% 3.71/0.89  fof(f346,plain,(
% 3.71/0.89    spl6_5 <=> sK0 = k9_relat_1(sK1,sK0)),
% 3.71/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 3.71/0.89  fof(f482,plain,(
% 3.71/0.89    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~spl6_5),
% 3.71/0.89    inference(subsumption_resolution,[],[f481,f125])).
% 3.71/0.89  fof(f481,plain,(
% 3.71/0.89    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | ~spl6_5),
% 3.71/0.89    inference(subsumption_resolution,[],[f480,f126])).
% 3.71/0.89  fof(f126,plain,(
% 3.71/0.89    v1_funct_2(sK1,sK0,sK0)),
% 3.71/0.89    inference(cnf_transformation,[],[f107])).
% 3.71/0.89  fof(f480,plain,(
% 3.71/0.89    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_5),
% 3.71/0.89    inference(subsumption_resolution,[],[f479,f128])).
% 3.71/0.89  fof(f479,plain,(
% 3.71/0.89    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_5),
% 3.71/0.89    inference(subsumption_resolution,[],[f464,f248])).
% 3.71/0.89  fof(f464,plain,(
% 3.71/0.89    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_5),
% 3.71/0.89    inference(trivial_inequality_removal,[],[f461])).
% 3.71/0.89  fof(f461,plain,(
% 3.71/0.89    sK0 != sK0 | k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl6_5),
% 3.71/0.89    inference(superposition,[],[f200,f445])).
% 3.71/0.89  fof(f445,plain,(
% 3.71/0.89    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl6_5),
% 3.71/0.89    inference(backward_demodulation,[],[f259,f347])).
% 3.71/0.89  fof(f347,plain,(
% 3.71/0.89    sK0 = k9_relat_1(sK1,sK0) | ~spl6_5),
% 3.71/0.89    inference(avatar_component_clause,[],[f346])).
% 3.71/0.89  fof(f259,plain,(
% 3.71/0.89    k2_relset_1(sK0,sK0,sK1) = k9_relat_1(sK1,sK0)),
% 3.71/0.89    inference(forward_demodulation,[],[f244,f250])).
% 3.71/0.89  fof(f250,plain,(
% 3.71/0.89    ( ! [X0] : (k7_relset_1(sK0,sK0,sK1,X0) = k9_relat_1(sK1,X0)) )),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f128,f203])).
% 3.71/0.89  fof(f203,plain,(
% 3.71/0.89    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.89    inference(cnf_transformation,[],[f101])).
% 3.71/0.89  fof(f101,plain,(
% 3.71/0.89    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.89    inference(ennf_transformation,[],[f34])).
% 3.71/0.89  fof(f34,axiom,(
% 3.71/0.89    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 3.71/0.89  fof(f244,plain,(
% 3.71/0.89    k2_relset_1(sK0,sK0,sK1) = k7_relset_1(sK0,sK0,sK1,sK0)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f128,f187])).
% 3.71/0.89  fof(f187,plain,(
% 3.71/0.89    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.89    inference(cnf_transformation,[],[f92])).
% 3.71/0.89  fof(f92,plain,(
% 3.71/0.89    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.89    inference(ennf_transformation,[],[f37])).
% 3.71/0.89  fof(f37,axiom,(
% 3.71/0.89    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 3.71/0.89  fof(f200,plain,(
% 3.71/0.89    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f99])).
% 3.71/0.89  fof(f99,plain,(
% 3.71/0.89    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.71/0.89    inference(flattening,[],[f98])).
% 3.71/0.89  fof(f98,plain,(
% 3.71/0.89    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.71/0.89    inference(ennf_transformation,[],[f47])).
% 3.71/0.89  fof(f47,axiom,(
% 3.71/0.89    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 3.71/0.89  fof(f475,plain,(
% 3.71/0.89    ~spl6_1 | spl6_2 | ~spl6_4),
% 3.71/0.89    inference(avatar_contradiction_clause,[],[f474])).
% 3.71/0.89  fof(f474,plain,(
% 3.71/0.89    $false | (~spl6_1 | spl6_2 | ~spl6_4)),
% 3.71/0.89    inference(subsumption_resolution,[],[f473,f471])).
% 3.71/0.89  fof(f471,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl6_2),
% 3.71/0.89    inference(forward_demodulation,[],[f470,f322])).
% 3.71/0.89  fof(f322,plain,(
% 3.71/0.89    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 3.71/0.89    inference(forward_demodulation,[],[f313,f286])).
% 3.71/0.89  fof(f286,plain,(
% 3.71/0.89    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 3.71/0.89    inference(backward_demodulation,[],[f280,f284])).
% 3.71/0.89  fof(f280,plain,(
% 3.71/0.89    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f241,f125,f248,f213])).
% 3.71/0.89  fof(f213,plain,(
% 3.71/0.89    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.89    inference(definition_unfolding,[],[f149,f132])).
% 3.71/0.89  fof(f149,plain,(
% 3.71/0.89    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f65])).
% 3.71/0.89  fof(f313,plain,(
% 3.71/0.89    k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f125,f265,f128,f262,f206])).
% 3.71/0.89  fof(f206,plain,(
% 3.71/0.89    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f105])).
% 3.71/0.89  fof(f105,plain,(
% 3.71/0.89    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.71/0.89    inference(flattening,[],[f104])).
% 3.71/0.89  fof(f104,plain,(
% 3.71/0.89    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.71/0.89    inference(ennf_transformation,[],[f44])).
% 3.71/0.89  fof(f44,axiom,(
% 3.71/0.89    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 3.71/0.89  fof(f262,plain,(
% 3.71/0.89    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.71/0.89    inference(forward_demodulation,[],[f239,f240])).
% 3.71/0.89  fof(f240,plain,(
% 3.71/0.89    k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f125,f126,f127,f128,f164])).
% 3.71/0.89  fof(f164,plain,(
% 3.71/0.89    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f80])).
% 3.71/0.89  fof(f80,plain,(
% 3.71/0.89    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.71/0.89    inference(flattening,[],[f79])).
% 3.71/0.89  fof(f79,plain,(
% 3.71/0.89    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.71/0.89    inference(ennf_transformation,[],[f45])).
% 3.71/0.89  fof(f45,axiom,(
% 3.71/0.89    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 3.71/0.89  fof(f239,plain,(
% 3.71/0.89    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f125,f126,f127,f128,f168])).
% 3.71/0.89  fof(f168,plain,(
% 3.71/0.89    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f82])).
% 3.71/0.89  fof(f82,plain,(
% 3.71/0.89    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.71/0.89    inference(flattening,[],[f81])).
% 3.71/0.89  fof(f81,plain,(
% 3.71/0.89    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.71/0.89    inference(ennf_transformation,[],[f42])).
% 3.71/0.89  fof(f42,axiom,(
% 3.71/0.89    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 3.71/0.89  fof(f265,plain,(
% 3.71/0.89    v1_funct_1(k2_funct_1(sK1))),
% 3.71/0.89    inference(forward_demodulation,[],[f236,f240])).
% 3.71/0.89  fof(f236,plain,(
% 3.71/0.89    v1_funct_1(k2_funct_2(sK0,sK1))),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f125,f126,f127,f128,f165])).
% 3.71/0.89  fof(f165,plain,(
% 3.71/0.89    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f82])).
% 3.71/0.89  fof(f470,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | spl6_2),
% 3.71/0.89    inference(forward_demodulation,[],[f234,f240])).
% 3.71/0.89  fof(f234,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | spl6_2),
% 3.71/0.89    inference(avatar_component_clause,[],[f232])).
% 3.71/0.89  fof(f232,plain,(
% 3.71/0.89    spl6_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 3.71/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.71/0.89  fof(f473,plain,(
% 3.71/0.89    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (~spl6_1 | ~spl6_4)),
% 3.71/0.89    inference(forward_demodulation,[],[f472,f447])).
% 3.71/0.89  fof(f447,plain,(
% 3.71/0.89    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | ~spl6_4),
% 3.71/0.89    inference(backward_demodulation,[],[f320,f446])).
% 3.71/0.89  fof(f446,plain,(
% 3.71/0.89    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK1)) | ~spl6_4),
% 3.71/0.89    inference(backward_demodulation,[],[f279,f344])).
% 3.71/0.89  fof(f344,plain,(
% 3.71/0.89    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~spl6_4),
% 3.71/0.89    inference(avatar_component_clause,[],[f342])).
% 3.71/0.89  fof(f320,plain,(
% 3.71/0.89    k6_partfun1(k1_relat_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 3.71/0.89    inference(forward_demodulation,[],[f316,f279])).
% 3.71/0.89  fof(f316,plain,(
% 3.71/0.89    k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f125,f128,f265,f262,f206])).
% 3.71/0.89  fof(f472,plain,(
% 3.71/0.89    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~spl6_1),
% 3.71/0.89    inference(forward_demodulation,[],[f229,f240])).
% 3.71/0.89  fof(f229,plain,(
% 3.71/0.89    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | ~spl6_1),
% 3.71/0.89    inference(avatar_component_clause,[],[f228])).
% 3.71/0.89  fof(f228,plain,(
% 3.71/0.89    spl6_1 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.71/0.89    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.71/0.89  fof(f469,plain,(
% 3.71/0.89    spl6_1 | ~spl6_4),
% 3.71/0.89    inference(avatar_contradiction_clause,[],[f468])).
% 3.71/0.89  fof(f468,plain,(
% 3.71/0.89    $false | (spl6_1 | ~spl6_4)),
% 3.71/0.89    inference(subsumption_resolution,[],[f465,f137])).
% 3.71/0.89  fof(f137,plain,(
% 3.71/0.89    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.71/0.89    inference(cnf_transformation,[],[f51])).
% 3.71/0.89  fof(f51,plain,(
% 3.71/0.89    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.71/0.89    inference(pure_predicate_removal,[],[f43])).
% 3.71/0.89  fof(f43,axiom,(
% 3.71/0.89    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 3.71/0.89  fof(f465,plain,(
% 3.71/0.89    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (spl6_1 | ~spl6_4)),
% 3.71/0.89    inference(unit_resulting_resolution,[],[f448,f226])).
% 3.71/0.89  fof(f226,plain,(
% 3.71/0.89    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.89    inference(duplicate_literal_removal,[],[f223])).
% 3.71/0.89  fof(f223,plain,(
% 3.71/0.89    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.89    inference(equality_resolution,[],[f205])).
% 3.71/0.89  fof(f205,plain,(
% 3.71/0.89    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.89    inference(cnf_transformation,[],[f124])).
% 3.71/0.89  fof(f124,plain,(
% 3.71/0.89    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.89    inference(nnf_transformation,[],[f103])).
% 3.71/0.89  fof(f103,plain,(
% 3.71/0.89    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.89    inference(flattening,[],[f102])).
% 3.71/0.89  fof(f102,plain,(
% 3.71/0.89    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.71/0.89    inference(ennf_transformation,[],[f35])).
% 3.71/0.89  fof(f35,axiom,(
% 3.71/0.89    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 3.71/0.89  fof(f448,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (spl6_1 | ~spl6_4)),
% 3.71/0.89    inference(backward_demodulation,[],[f281,f446])).
% 3.71/0.89  fof(f281,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) | spl6_1),
% 3.71/0.89    inference(backward_demodulation,[],[f270,f279])).
% 3.71/0.89  fof(f270,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl6_1),
% 3.71/0.89    inference(subsumption_resolution,[],[f269,f125])).
% 3.71/0.89  fof(f269,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~v1_funct_1(sK1) | spl6_1),
% 3.71/0.89    inference(subsumption_resolution,[],[f268,f128])).
% 3.71/0.89  fof(f268,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl6_1),
% 3.71/0.89    inference(subsumption_resolution,[],[f267,f265])).
% 3.71/0.89  fof(f267,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl6_1),
% 3.71/0.89    inference(subsumption_resolution,[],[f266,f262])).
% 3.71/0.89  fof(f266,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl6_1),
% 3.71/0.89    inference(superposition,[],[f261,f206])).
% 3.71/0.89  fof(f261,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl6_1),
% 3.71/0.89    inference(backward_demodulation,[],[f230,f240])).
% 3.71/0.89  fof(f230,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | spl6_1),
% 3.71/0.89    inference(avatar_component_clause,[],[f228])).
% 3.71/0.89  fof(f443,plain,(
% 3.71/0.89    spl6_5),
% 3.71/0.89    inference(avatar_split_clause,[],[f440,f346])).
% 3.71/0.89  fof(f440,plain,(
% 3.71/0.89    sK0 = k9_relat_1(sK1,sK0)),
% 3.71/0.89    inference(forward_demodulation,[],[f439,f284])).
% 3.71/0.89  fof(f439,plain,(
% 3.71/0.89    k2_relat_1(sK1) = k9_relat_1(sK1,sK0)),
% 3.71/0.89    inference(subsumption_resolution,[],[f436,f241])).
% 3.71/0.89  fof(f436,plain,(
% 3.71/0.89    k2_relat_1(sK1) = k9_relat_1(sK1,sK0) | ~v1_relat_1(sK1)),
% 3.71/0.89    inference(superposition,[],[f153,f282])).
% 3.71/0.89  fof(f153,plain,(
% 3.71/0.89    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f68])).
% 3.71/0.89  fof(f68,plain,(
% 3.71/0.89    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.71/0.89    inference(ennf_transformation,[],[f23])).
% 3.71/0.89  fof(f23,axiom,(
% 3.71/0.89    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 3.71/0.89  fof(f399,plain,(
% 3.71/0.89    spl6_6 | ~spl6_3),
% 3.71/0.89    inference(avatar_split_clause,[],[f394,f338,f396])).
% 3.71/0.89  fof(f394,plain,(
% 3.71/0.89    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 3.71/0.89    inference(subsumption_resolution,[],[f384,f241])).
% 3.71/0.89  fof(f384,plain,(
% 3.71/0.89    k1_xboole_0 != sK0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1)),
% 3.71/0.89    inference(superposition,[],[f141,f284])).
% 3.71/0.89  fof(f141,plain,(
% 3.71/0.89    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.89    inference(cnf_transformation,[],[f55])).
% 3.71/0.89  fof(f55,plain,(
% 3.71/0.89    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.71/0.89    inference(flattening,[],[f54])).
% 3.71/0.89  fof(f54,plain,(
% 3.71/0.89    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.71/0.89    inference(ennf_transformation,[],[f25])).
% 3.71/0.89  fof(f25,axiom,(
% 3.71/0.89    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.71/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 3.71/0.89  fof(f235,plain,(
% 3.71/0.89    ~spl6_1 | ~spl6_2),
% 3.71/0.89    inference(avatar_split_clause,[],[f129,f232,f228])).
% 3.71/0.89  fof(f129,plain,(
% 3.71/0.89    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.71/0.89    inference(cnf_transformation,[],[f107])).
% 3.71/0.89  % SZS output end Proof for theBenchmark
% 3.71/0.89  % (18811)------------------------------
% 3.71/0.89  % (18811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.71/0.89  % (18811)Termination reason: Refutation
% 3.71/0.89  
% 3.71/0.89  % (18811)Memory used [KB]: 11897
% 3.71/0.89  % (18811)Time elapsed: 0.454 s
% 3.71/0.89  % (18811)------------------------------
% 3.71/0.89  % (18811)------------------------------
% 3.71/0.89  % (18784)Success in time 0.526 s
%------------------------------------------------------------------------------
