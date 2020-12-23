%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0805+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:41 EST 2020

% Result     : Theorem 3.81s
% Output     : Refutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 471 expanded)
%              Number of leaves         :   29 ( 136 expanded)
%              Depth                    :   18
%              Number of atoms          :  640 (1537 expanded)
%              Number of equality atoms :   66 ( 168 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4689,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f137,f142,f152,f251,f257,f1595,f1923,f3029,f4257,f4403,f4688])).

fof(f4688,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_10
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f4687])).

fof(f4687,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f4686,f1576])).

fof(f1576,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK1)) != k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f1575])).

fof(f1575,plain,
    ( spl8_10
  <=> k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f4686,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(resolution,[],[f4452,f275])).

fof(f275,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_wellord1(sK2,X1))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(condensation,[],[f274])).

fof(f274,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_wellord1(sK2,X1))
        | ~ r2_hidden(X1,k1_wellord1(sK2,X0)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(superposition,[],[f271,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0)
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f121,f101])).

fof(f101,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl8_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | k1_wellord1(sK2,X0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f106,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X0,k1_wellord1(X2,X1))
          & v2_wellord1(X2) )
       => k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_wellord1)).

fof(f106,plain,
    ( v2_wellord1(sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl8_2
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f271,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k1_wellord1(k2_wellord1(sK2,X1),X0))
    | ~ spl8_1 ),
    inference(resolution,[],[f160,f97])).

fof(f97,plain,(
    ! [X0,X3] : ~ sP6(X3,X3,X0) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( X1 != X3
      | ~ sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f160,plain,
    ( ! [X17,X18,X16] :
        ( sP6(X16,X17,k2_wellord1(sK2,X18))
        | ~ r2_hidden(X16,k1_wellord1(k2_wellord1(sK2,X18),X17)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f117,f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f117,plain,
    ( ! [X7] : v1_relat_1(k2_wellord1(sK2,X7))
    | ~ spl8_1 ),
    inference(resolution,[],[f101,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f4452,plain,
    ( ! [X21] :
        ( r2_hidden(sK1,k1_wellord1(sK2,X21))
        | k2_wellord1(sK2,k1_wellord1(sK2,X21)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,X21)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(resolution,[],[f1594,f4212])).

fof(f4212,plain,
    ( ! [X10,X11,X9] :
        ( ~ r2_hidden(X9,k1_wellord1(sK2,X11))
        | r2_hidden(X9,k1_wellord1(sK2,X10))
        | k2_wellord1(sK2,k1_wellord1(sK2,X10)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X11)),k1_wellord1(sK2,X10)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f4208,f118])).

fof(f118,plain,
    ( ! [X8,X9] :
        ( ~ r1_tarski(X8,X9)
        | k2_wellord1(k2_wellord1(sK2,X9),X8) = k2_wellord1(sK2,X8) )
    | ~ spl8_1 ),
    inference(resolution,[],[f101,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f4208,plain,
    ( ! [X0,X3,X1] :
        ( r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1))
        | r2_hidden(X3,k1_wellord1(sK2,X0))
        | ~ r2_hidden(X3,k1_wellord1(sK2,X1)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(condensation,[],[f4207])).

fof(f4207,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1))
        | ~ r2_hidden(X2,k1_wellord1(sK2,X1))
        | r2_hidden(X3,k1_wellord1(sK2,X0))
        | ~ r2_hidden(X3,k1_wellord1(sK2,X1)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(factoring,[],[f729])).

fof(f729,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( r1_tarski(k1_wellord1(sK2,X3),k1_wellord1(sK2,X4))
        | ~ r2_hidden(X5,k1_wellord1(sK2,X4))
        | r2_hidden(X6,k1_wellord1(sK2,X3))
        | ~ r2_hidden(X6,k1_wellord1(sK2,X7))
        | r1_tarski(k1_wellord1(sK2,X3),k1_wellord1(sK2,X7)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f409,f359])).

fof(f359,plain,
    ( ! [X4,X5,X3] :
        ( m1_subset_1(X5,k1_wellord1(sK2,X3))
        | ~ r2_hidden(X5,k1_wellord1(sK2,X4))
        | r1_tarski(k1_wellord1(sK2,X3),k1_wellord1(sK2,X4)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f277,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f277,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k1_wellord1(sK2,X3),k1_zfmisc_1(k1_wellord1(sK2,X2)))
        | r1_tarski(k1_wellord1(sK2,X2),k1_wellord1(sK2,X3)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f175,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f175,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1))
        | r1_tarski(k1_wellord1(sK2,X1),k1_wellord1(sK2,X0)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f128,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f128,plain,
    ( ! [X2,X3] : r3_xboole_0(k1_wellord1(sK2,X2),k1_wellord1(sK2,X3))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f122,f101])).

fof(f122,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK2)
        | r3_xboole_0(k1_wellord1(sK2,X2),k1_wellord1(sK2,X3)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f106,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2)
      | r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord1)).

fof(f409,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_wellord1(sK2,X2))
        | r1_tarski(k1_wellord1(sK2,X2),k1_wellord1(sK2,X1))
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | r2_hidden(X3,k1_wellord1(sK2,X2)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f358,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f358,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(k1_wellord1(sK2,X0))
        | ~ r2_hidden(X2,k1_wellord1(sK2,X1))
        | r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f277,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f1594,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f1592])).

fof(f1592,plain,
    ( spl8_12
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f4403,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f4402])).

fof(f4402,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f4401,f1580])).

fof(f1580,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f1579])).

fof(f1579,plain,
    ( spl8_11
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f4401,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f4267,f151])).

fof(f151,plain,
    ( r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl8_7
  <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f4267,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(superposition,[],[f427,f3028])).

fof(f3028,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f3026])).

fof(f3026,plain,
    ( spl8_20
  <=> k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f427,plain,
    ( ! [X0,X1] :
        ( ~ r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),k1_wellord1(sK2,X0)),k2_wellord1(sK2,k1_wellord1(sK2,X1)))
        | ~ r2_hidden(X0,k1_wellord1(sK2,X1)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f425,f117])).

fof(f425,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),k1_wellord1(sK2,X0)),k2_wellord1(sK2,k1_wellord1(sK2,X1)))
        | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X1))) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f303,f177])).

fof(f177,plain,
    ( ! [X6,X4,X5] :
        ( r4_wellord1(X4,k2_wellord1(k2_wellord1(sK2,X5),X6))
        | ~ r4_wellord1(k2_wellord1(k2_wellord1(sK2,X5),X6),X4)
        | ~ v1_relat_1(X4) )
    | ~ spl8_1 ),
    inference(resolution,[],[f158,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f158,plain,
    ( ! [X12,X11] : v1_relat_1(k2_wellord1(k2_wellord1(sK2,X11),X12))
    | ~ spl8_1 ),
    inference(resolution,[],[f117,f80])).

fof(f303,plain,
    ( ! [X0,X1] :
        ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X0)),k1_wellord1(sK2,X1)))
        | ~ r2_hidden(X1,k1_wellord1(sK2,X0)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_wellord1(sK2,X0))
        | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X0)),k1_wellord1(sK2,X1)))
        | ~ r2_hidden(X1,k1_wellord1(sK2,X0)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f301,f129])).

fof(f129,plain,
    ( ! [X4] : k1_wellord1(sK2,X4) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X4)))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f123,f101])).

fof(f123,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(sK2)
        | k1_wellord1(sK2,X4) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X4))) )
    | ~ spl8_2 ),
    inference(resolution,[],[f106,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

fof(f301,plain,
    ( ! [X0,X1] :
        ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X0)),k1_wellord1(sK2,X1)))
        | ~ r2_hidden(X1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0))))
        | ~ r2_hidden(X1,k1_wellord1(sK2,X0)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(superposition,[],[f173,f127])).

fof(f173,plain,
    ( ! [X12,X11] :
        ( ~ r4_wellord1(k2_wellord1(sK2,X11),k2_wellord1(k2_wellord1(sK2,X11),k1_wellord1(k2_wellord1(sK2,X11),X12)))
        | ~ r2_hidden(X12,k3_relat_1(k2_wellord1(sK2,X11))) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f167,f117])).

fof(f167,plain,
    ( ! [X12,X11] :
        ( ~ v1_relat_1(k2_wellord1(sK2,X11))
        | ~ r2_hidden(X12,k3_relat_1(k2_wellord1(sK2,X11)))
        | ~ r4_wellord1(k2_wellord1(sK2,X11),k2_wellord1(k2_wellord1(sK2,X11),k1_wellord1(k2_wellord1(sK2,X11),X12))) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f130,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(f130,plain,
    ( ! [X5] : v2_wellord1(k2_wellord1(sK2,X5))
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f124,f101])).

fof(f124,plain,
    ( ! [X5] :
        ( ~ v1_relat_1(sK2)
        | v2_wellord1(k2_wellord1(sK2,X5)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f106,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | v2_wellord1(k2_wellord1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_wellord1)).

fof(f4257,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11
    | spl8_20 ),
    inference(avatar_contradiction_clause,[],[f4256])).

fof(f4256,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11
    | spl8_20 ),
    inference(subsumption_resolution,[],[f4255,f3027])).

fof(f3027,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK0)) != k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | spl8_20 ),
    inference(avatar_component_clause,[],[f3026])).

fof(f4255,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11 ),
    inference(resolution,[],[f4231,f275])).

fof(f4231,plain,
    ( ! [X2] :
        ( r2_hidden(sK0,k1_wellord1(sK2,X2))
        | k2_wellord1(sK2,k1_wellord1(sK2,X2)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,X2)) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_11 ),
    inference(resolution,[],[f4212,f1580])).

fof(f3029,plain,
    ( spl8_20
    | ~ spl8_1
    | ~ spl8_2
    | spl8_10 ),
    inference(avatar_split_clause,[],[f2889,f1575,f104,f99,f3026])).

fof(f2889,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | ~ spl8_1
    | ~ spl8_2
    | spl8_10 ),
    inference(trivial_inequality_removal,[],[f2888])).

fof(f2888,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK1)) != k2_wellord1(sK2,k1_wellord1(sK2,sK1))
    | k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | ~ spl8_1
    | ~ spl8_2
    | spl8_10 ),
    inference(superposition,[],[f1576,f454])).

fof(f454,plain,
    ( ! [X8,X7] :
        ( k2_wellord1(sK2,k1_wellord1(sK2,X7)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X8)),k1_wellord1(sK2,X7))
        | k2_wellord1(sK2,k1_wellord1(sK2,X8)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X7)),k1_wellord1(sK2,X8)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f276,f118])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1))
        | k2_wellord1(sK2,k1_wellord1(sK2,X1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X0)),k1_wellord1(sK2,X1)) )
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(resolution,[],[f175,f118])).

fof(f1923,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(avatar_contradiction_clause,[],[f1922])).

fof(f1922,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f1921,f1594])).

fof(f1921,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f1821,f151])).

fof(f1821,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(superposition,[],[f303,f1577])).

fof(f1577,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f1575])).

fof(f1595,plain,
    ( spl8_12
    | ~ spl8_1
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_9
    | spl8_11 ),
    inference(avatar_split_clause,[],[f1587,f1579,f249,f139,f134,f109,f99,f1592])).

fof(f109,plain,
    ( spl8_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f134,plain,
    ( spl8_4
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f139,plain,
    ( spl8_5
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f249,plain,
    ( spl8_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f1587,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl8_1
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_9
    | spl8_11 ),
    inference(subsumption_resolution,[],[f1586,f111])).

fof(f111,plain,
    ( sK0 != sK1
    | spl8_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1586,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | sK0 = sK1
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_9
    | spl8_11 ),
    inference(subsumption_resolution,[],[f1585,f141])).

fof(f141,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f1585,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | sK0 = sK1
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_9
    | spl8_11 ),
    inference(resolution,[],[f1581,f679])).

fof(f679,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k1_wellord1(sK2,X0))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(X0,k1_wellord1(sK2,sK0))
        | sK0 = X0 )
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(resolution,[],[f561,f136])).

fof(f136,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f561,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | X1 = X2
        | ~ r2_hidden(X2,k3_relat_1(sK2))
        | r2_hidden(X2,k1_wellord1(sK2,X1))
        | r2_hidden(X1,k1_wellord1(sK2,X2)) )
    | ~ spl8_1
    | ~ spl8_9 ),
    inference(resolution,[],[f394,f120])).

fof(f120,plain,
    ( ! [X12,X13] :
        ( ~ sP6(X12,X13,sK2)
        | r2_hidden(X12,k1_wellord1(sK2,X13)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f101,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP6(X3,X1,X0)
      | r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f394,plain,
    ( ! [X2,X1] :
        ( sP6(X2,X1,sK2)
        | ~ r2_hidden(X2,k3_relat_1(sK2))
        | X1 = X2
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(X1,k1_wellord1(sK2,X2)) )
    | ~ spl8_1
    | ~ spl8_9 ),
    inference(resolution,[],[f305,f120])).

fof(f305,plain,
    ( ! [X0,X1] :
        ( sP6(X0,X1,sK2)
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | sP6(X1,X0,sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2)) )
    | ~ spl8_9 ),
    inference(duplicate_literal_removal,[],[f304])).

fof(f304,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | sP6(X1,X0,sK2)
        | X0 = X1
        | sP6(X0,X1,sK2) )
    | ~ spl8_9 ),
    inference(resolution,[],[f263,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | X1 = X3
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f263,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | sP6(X1,X0,sK2) )
    | ~ spl8_9 ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1
        | sP6(X1,X0,sK2) )
    | ~ spl8_9 ),
    inference(resolution,[],[f250,f72])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2)) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f249])).

fof(f1581,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | spl8_11 ),
    inference(avatar_component_clause,[],[f1579])).

fof(f257,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | spl8_8 ),
    inference(subsumption_resolution,[],[f255,f106])).

fof(f255,plain,
    ( ~ v2_wellord1(sK2)
    | ~ spl8_1
    | spl8_8 ),
    inference(subsumption_resolution,[],[f252,f101])).

fof(f252,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_wellord1(sK2)
    | spl8_8 ),
    inference(resolution,[],[f247,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f247,plain,
    ( ~ v6_relat_2(sK2)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl8_8
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f251,plain,
    ( ~ spl8_8
    | spl8_9
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f113,f99,f249,f245])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ v6_relat_2(sK2) )
    | ~ spl8_1 ),
    inference(resolution,[],[f101,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f152,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f55,f149])).

fof(f55,plain,(
    r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
      & X0 != X1
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
      & X0 != X1
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
            & X0 != X1
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
          & X0 != X1
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_wellord1)).

fof(f142,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f53,f139])).

fof(f53,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f137,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f52,f134])).

fof(f52,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f112,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f54,f109])).

fof(f54,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f107,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f51,f104])).

fof(f51,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f50,f99])).

fof(f50,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

%------------------------------------------------------------------------------
