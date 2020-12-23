%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 432 expanded)
%              Number of leaves         :   47 ( 185 expanded)
%              Depth                    :   12
%              Number of atoms          :  680 (2541 expanded)
%              Number of equality atoms :  111 ( 712 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1714,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f131,f136,f163,f168,f250,f262,f285,f291,f311,f326,f347,f360,f373,f398,f524,f535,f577,f776,f1428,f1429,f1494,f1585,f1713])).

fof(f1713,plain,
    ( k1_xboole_0 != sK2
    | sK0 != k1_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1585,plain,
    ( ~ spl8_2
    | ~ spl8_59 ),
    inference(avatar_contradiction_clause,[],[f1510])).

fof(f1510,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_59 ),
    inference(subsumption_resolution,[],[f130,f1496])).

fof(f1496,plain,
    ( ! [X2,X0] : ~ r2_hidden(X2,X0)
    | ~ spl8_59 ),
    inference(subsumption_resolution,[],[f66,f1489])).

fof(f1489,plain,
    ( ! [X0] : v1_xboole_0(X0)
    | ~ spl8_59 ),
    inference(avatar_component_clause,[],[f1488])).

fof(f1488,plain,
    ( spl8_59
  <=> ! [X0] : v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f130,plain,
    ( r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl8_2
  <=> r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1494,plain,
    ( spl8_59
    | spl8_60
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f1481,f396,f392,f1491,f1488])).

fof(f1491,plain,
    ( spl8_60
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f392,plain,
    ( spl8_19
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f396,plain,
    ( spl8_20
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f1481,plain,
    ( ! [X0] :
        ( v1_partfun1(k1_xboole_0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1480,f149])).

fof(f149,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f102,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1480,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_partfun1(k1_xboole_0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f1479,f105])).

fof(f105,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1479,plain,
    ( ! [X0] :
        ( v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_xboole_0(X0) )
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f1478,f393])).

fof(f393,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f392])).

fof(f1478,plain,
    ( ! [X0] :
        ( v1_partfun1(k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_xboole_0(X0) )
    | ~ spl8_20 ),
    inference(resolution,[],[f397,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f397,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f396])).

fof(f1429,plain,
    ( sK2 != sK7(sK0,sK1,sK2)
    | k1_xboole_0 != sK2
    | v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(sK7(sK0,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1428,plain,
    ( spl8_53
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f854,f773,f1425])).

fof(f1425,plain,
    ( spl8_53
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f773,plain,
    ( spl8_29
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f854,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f775,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f775,plain,
    ( v1_xboole_0(sK2)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f773])).

fof(f776,plain,
    ( spl8_29
    | ~ spl8_18
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f671,f574,f370,f773])).

fof(f370,plain,
    ( spl8_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f574,plain,
    ( spl8_25
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f671,plain,
    ( v1_xboole_0(sK2)
    | ~ spl8_18
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f372,f576,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f576,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f574])).

fof(f372,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f370])).

fof(f577,plain,
    ( spl8_25
    | ~ spl8_2
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f530,f344,f308,f259,f160,f156,f152,f128,f574])).

fof(f152,plain,
    ( spl8_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f156,plain,
    ( spl8_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f160,plain,
    ( spl8_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f259,plain,
    ( spl8_11
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f308,plain,
    ( spl8_13
  <=> v1_relat_1(sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f344,plain,
    ( spl8_15
  <=> v1_funct_2(sK2,sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f530,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl8_2
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f350,f525])).

fof(f525,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f153,f158,f161,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f161,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f160])).

fof(f158,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f153,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f350,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_13
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f349,f320])).

fof(f320,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f305,f312])).

fof(f312,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_2
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f310,f182])).

fof(f182,plain,
    ( sK2 = sK7(sK0,sK1,sK2)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f130,f118])).

fof(f118,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | sK7(X0,X1,X6) = X6 ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X6,X2,X0,X1] :
      ( sK7(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK5(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X1)
              & k1_relat_1(sK6(X0,X1,X2)) = X0
              & sK5(X0,X1,X2) = sK6(X0,X1,X2)
              & v1_funct_1(sK6(X0,X1,X2))
              & v1_relat_1(sK6(X0,X1,X2)) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1)
                & k1_relat_1(sK7(X0,X1,X6)) = X0
                & sK7(X0,X1,X6) = X6
                & v1_funct_1(sK7(X0,X1,X6))
                & v1_relat_1(sK7(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f50,f53,f52,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & k1_relat_1(X5) = X0
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | k1_relat_1(X4) != X0
              | sK5(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK5(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK5(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X1)
        & k1_relat_1(sK6(X0,X1,X2)) = X0
        & sK5(X0,X1,X2) = sK6(X0,X1,X2)
        & v1_funct_1(sK6(X0,X1,X2))
        & v1_relat_1(sK6(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1)
        & k1_relat_1(sK7(X0,X1,X6)) = X0
        & sK7(X0,X1,X6) = X6
        & v1_funct_1(sK7(X0,X1,X6))
        & v1_relat_1(sK7(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & k1_relat_1(X5) = X0
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & k1_relat_1(X8) = X0
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

fof(f310,plain,
    ( v1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f308])).

fof(f305,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2)
    | ~ spl8_5
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f296,f261])).

fof(f261,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f259])).

fof(f296,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f153,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f349,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl8_5
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f348,f153])).

fof(f348,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl8_15 ),
    inference(resolution,[],[f346,f70])).

fof(f346,plain,
    ( v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f344])).

fof(f535,plain,
    ( ~ spl8_23
    | ~ spl8_5
    | spl8_6
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f525,f160,f156,f152,f532])).

fof(f532,plain,
    ( spl8_23
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f524,plain,
    ( spl8_7
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f340,f323,f259,f247,f160])).

fof(f247,plain,
    ( spl8_10
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f323,plain,
    ( spl8_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f340,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_10
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f333,f261])).

fof(f333,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl8_10
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f249,f102,f325,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f325,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f323])).

fof(f249,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f247])).

fof(f398,plain,
    ( ~ spl8_19
    | spl8_20
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f228,f165,f133,f123,f396,f392])).

fof(f123,plain,
    ( spl8_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f133,plain,
    ( spl8_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f165,plain,
    ( spl8_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f228,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f227,f167])).

fof(f167,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f227,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f226,f145])).

fof(f145,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f125,f66])).

fof(f125,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f226,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_xboole_0,X0,k1_xboole_0),k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_3 ),
    inference(superposition,[],[f109,f135])).

fof(f135,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f109,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f373,plain,
    ( spl8_18
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f320,f308,f259,f152,f128,f370])).

fof(f360,plain,
    ( spl8_17
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f182,f128,f357])).

fof(f357,plain,
    ( spl8_17
  <=> sK2 = sK7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

% (478)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f347,plain,
    ( spl8_15
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f321,f308,f259,f152,f128,f344])).

fof(f321,plain,
    ( v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ spl8_2
    | ~ spl8_5
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f306,f312])).

fof(f306,plain,
    ( v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl8_5
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f297,f261])).

fof(f297,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f153,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f326,plain,
    ( spl8_14
    | ~ spl8_2
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f312,f308,f128,f323])).

% (458)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f311,plain,
    ( spl8_13
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f179,f128,f308])).

fof(f179,plain,
    ( v1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f130,f120])).

fof(f120,plain,(
    ! [X6,X0,X1] :
      ( v1_relat_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f291,plain,
    ( spl8_5
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f286,f282,f128,f152])).

fof(f282,plain,
    ( spl8_12
  <=> v1_funct_1(sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f286,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f284,f182])).

fof(f284,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f282])).

fof(f285,plain,
    ( spl8_12
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f176,f128,f282])).

fof(f176,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f130,f119])).

fof(f119,plain,(
    ! [X6,X0,X1] :
      ( v1_funct_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK7(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

% (456)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f262,plain,
    ( spl8_11
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f203,f128,f259])).

fof(f203,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f200,f182])).

fof(f200,plain,
    ( sK0 = k1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f130,f117])).

fof(f117,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | k1_relat_1(sK7(X0,X1,X6)) = X0 ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK7(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f250,plain,
    ( spl8_10
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f198,f128,f247])).

fof(f198,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f195,f182])).

fof(f195,plain,
    ( r1_tarski(k2_relat_1(sK7(sK0,sK1,sK2)),sK1)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f130,f116])).

fof(f116,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_funct_2(X0,X1))
      | r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f168,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f147,f165])).

fof(f147,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f68,f104])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f163,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f56,f160,f156,f152])).

fof(f56,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f136,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f58,f133])).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f131,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f55,f128])).

fof(f55,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f126,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f57,f123])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:44:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (483)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.46  % (461)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.47  % (461)Refutation not found, incomplete strategy% (461)------------------------------
% 0.20/0.47  % (461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (461)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (461)Memory used [KB]: 10618
% 0.20/0.47  % (461)Time elapsed: 0.059 s
% 0.20/0.47  % (461)------------------------------
% 0.20/0.47  % (461)------------------------------
% 0.20/0.50  % (477)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (457)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (465)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (467)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (455)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (459)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (475)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (466)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (462)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (463)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (471)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.53  % (473)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (469)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (483)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f1714,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f126,f131,f136,f163,f168,f250,f262,f285,f291,f311,f326,f347,f360,f373,f398,f524,f535,f577,f776,f1428,f1429,f1494,f1585,f1713])).
% 0.20/0.53  fof(f1713,plain,(
% 0.20/0.53    k1_xboole_0 != sK2 | sK0 != k1_relat_1(sK2) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_partfun1(sK2,sK0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f1585,plain,(
% 0.20/0.53    ~spl8_2 | ~spl8_59),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f1510])).
% 0.20/0.53  fof(f1510,plain,(
% 0.20/0.53    $false | (~spl8_2 | ~spl8_59)),
% 0.20/0.53    inference(subsumption_resolution,[],[f130,f1496])).
% 0.20/0.53  fof(f1496,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0)) ) | ~spl8_59),
% 0.20/0.53    inference(subsumption_resolution,[],[f66,f1489])).
% 0.20/0.53  fof(f1489,plain,(
% 0.20/0.53    ( ! [X0] : (v1_xboole_0(X0)) ) | ~spl8_59),
% 0.20/0.53    inference(avatar_component_clause,[],[f1488])).
% 0.20/0.53  fof(f1488,plain,(
% 0.20/0.53    spl8_59 <=> ! [X0] : v1_xboole_0(X0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(rectify,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    r2_hidden(sK2,k1_funct_2(sK0,sK1)) | ~spl8_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f128])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    spl8_2 <=> r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.53  fof(f1494,plain,(
% 0.20/0.53    spl8_59 | spl8_60 | ~spl8_19 | ~spl8_20),
% 0.20/0.53    inference(avatar_split_clause,[],[f1481,f396,f392,f1491,f1488])).
% 0.20/0.53  fof(f1491,plain,(
% 0.20/0.53    spl8_60 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).
% 0.20/0.53  fof(f392,plain,(
% 0.20/0.53    spl8_19 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.20/0.53  fof(f396,plain,(
% 0.20/0.53    spl8_20 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.20/0.53  fof(f1481,plain,(
% 0.20/0.53    ( ! [X0] : (v1_partfun1(k1_xboole_0,k1_xboole_0) | v1_xboole_0(X0)) ) | (~spl8_19 | ~spl8_20)),
% 0.20/0.53    inference(subsumption_resolution,[],[f1480,f149])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f102,f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f1480,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_partfun1(k1_xboole_0,k1_xboole_0) | v1_xboole_0(X0)) ) | (~spl8_19 | ~spl8_20)),
% 0.20/0.53    inference(forward_demodulation,[],[f1479,f105])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(flattening,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.53  fof(f1479,plain,(
% 0.20/0.53    ( ! [X0] : (v1_partfun1(k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_xboole_0(X0)) ) | (~spl8_19 | ~spl8_20)),
% 0.20/0.53    inference(subsumption_resolution,[],[f1478,f393])).
% 0.20/0.53  fof(f393,plain,(
% 0.20/0.53    v1_funct_1(k1_xboole_0) | ~spl8_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f392])).
% 0.20/0.53  fof(f1478,plain,(
% 0.20/0.53    ( ! [X0] : (v1_partfun1(k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_xboole_0(X0)) ) | ~spl8_20),
% 0.20/0.53    inference(resolution,[],[f397,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.53  fof(f397,plain,(
% 0.20/0.53    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl8_20),
% 0.20/0.53    inference(avatar_component_clause,[],[f396])).
% 0.20/0.53  fof(f1429,plain,(
% 0.20/0.53    sK2 != sK7(sK0,sK1,sK2) | k1_xboole_0 != sK2 | v1_funct_1(k1_xboole_0) | ~v1_funct_1(sK7(sK0,sK1,sK2))),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f1428,plain,(
% 0.20/0.53    spl8_53 | ~spl8_29),
% 0.20/0.53    inference(avatar_split_clause,[],[f854,f773,f1425])).
% 0.20/0.53  fof(f1425,plain,(
% 0.20/0.53    spl8_53 <=> k1_xboole_0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 0.20/0.53  fof(f773,plain,(
% 0.20/0.53    spl8_29 <=> v1_xboole_0(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.20/0.53  fof(f854,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | ~spl8_29),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f775,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.53  fof(f775,plain,(
% 0.20/0.53    v1_xboole_0(sK2) | ~spl8_29),
% 0.20/0.53    inference(avatar_component_clause,[],[f773])).
% 0.20/0.53  fof(f776,plain,(
% 0.20/0.53    spl8_29 | ~spl8_18 | ~spl8_25),
% 0.20/0.53    inference(avatar_split_clause,[],[f671,f574,f370,f773])).
% 0.20/0.53  fof(f370,plain,(
% 0.20/0.53    spl8_18 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.20/0.53  fof(f574,plain,(
% 0.20/0.53    spl8_25 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.20/0.53  fof(f671,plain,(
% 0.20/0.53    v1_xboole_0(sK2) | (~spl8_18 | ~spl8_25)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f372,f576,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.53  fof(f576,plain,(
% 0.20/0.53    v1_xboole_0(k2_relat_1(sK2)) | ~spl8_25),
% 0.20/0.53    inference(avatar_component_clause,[],[f574])).
% 0.20/0.53  fof(f372,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | ~spl8_18),
% 0.20/0.53    inference(avatar_component_clause,[],[f370])).
% 0.20/0.53  fof(f577,plain,(
% 0.20/0.53    spl8_25 | ~spl8_2 | ~spl8_5 | spl8_6 | ~spl8_7 | ~spl8_11 | ~spl8_13 | ~spl8_15),
% 0.20/0.53    inference(avatar_split_clause,[],[f530,f344,f308,f259,f160,f156,f152,f128,f574])).
% 0.20/0.53  fof(f152,plain,(
% 0.20/0.53    spl8_5 <=> v1_funct_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    spl8_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    spl8_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.53  fof(f259,plain,(
% 0.20/0.53    spl8_11 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.53  fof(f308,plain,(
% 0.20/0.53    spl8_13 <=> v1_relat_1(sK7(sK0,sK1,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.53  fof(f344,plain,(
% 0.20/0.53    spl8_15 <=> v1_funct_2(sK2,sK0,k2_relat_1(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.53  fof(f530,plain,(
% 0.20/0.53    v1_xboole_0(k2_relat_1(sK2)) | (~spl8_2 | ~spl8_5 | spl8_6 | ~spl8_7 | ~spl8_11 | ~spl8_13 | ~spl8_15)),
% 0.20/0.53    inference(subsumption_resolution,[],[f350,f525])).
% 0.20/0.53  fof(f525,plain,(
% 0.20/0.53    ~v1_partfun1(sK2,sK0) | (~spl8_5 | spl8_6 | ~spl8_7)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f153,f158,f161,f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f160])).
% 0.20/0.53  fof(f158,plain,(
% 0.20/0.53    ~v1_funct_2(sK2,sK0,sK1) | spl8_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f156])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    v1_funct_1(sK2) | ~spl8_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f152])).
% 0.20/0.53  fof(f350,plain,(
% 0.20/0.53    v1_partfun1(sK2,sK0) | v1_xboole_0(k2_relat_1(sK2)) | (~spl8_2 | ~spl8_5 | ~spl8_11 | ~spl8_13 | ~spl8_15)),
% 0.20/0.53    inference(subsumption_resolution,[],[f349,f320])).
% 0.20/0.53  fof(f320,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | (~spl8_2 | ~spl8_5 | ~spl8_11 | ~spl8_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f305,f312])).
% 0.20/0.53  fof(f312,plain,(
% 0.20/0.53    v1_relat_1(sK2) | (~spl8_2 | ~spl8_13)),
% 0.20/0.53    inference(forward_demodulation,[],[f310,f182])).
% 0.20/0.53  fof(f182,plain,(
% 0.20/0.53    sK2 = sK7(sK0,sK1,sK2) | ~spl8_2),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f130,f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_funct_2(X0,X1)) | sK7(X0,X1,X6) = X6) )),
% 0.20/0.53    inference(equality_resolution,[],[f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X6,X2,X0,X1] : (sK7(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK5(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X1) & k1_relat_1(sK6(X0,X1,X2)) = X0 & sK5(X0,X1,X2) = sK6(X0,X1,X2) & v1_funct_1(sK6(X0,X1,X2)) & v1_relat_1(sK6(X0,X1,X2))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1) & k1_relat_1(sK7(X0,X1,X6)) = X0 & sK7(X0,X1,X6) = X6 & v1_funct_1(sK7(X0,X1,X6)) & v1_relat_1(sK7(X0,X1,X6))) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f50,f53,f52,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK5(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK5(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK5(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK6(X0,X1,X2)),X1) & k1_relat_1(sK6(X0,X1,X2)) = X0 & sK5(X0,X1,X2) = sK6(X0,X1,X2) & v1_funct_1(sK6(X0,X1,X2)) & v1_relat_1(sK6(X0,X1,X2))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1) & k1_relat_1(sK7(X0,X1,X6)) = X0 & sK7(X0,X1,X6) = X6 & v1_funct_1(sK7(X0,X1,X6)) & v1_relat_1(sK7(X0,X1,X6))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.20/0.53    inference(rectify,[],[f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.20/0.53    inference(nnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).
% 0.20/0.53  fof(f310,plain,(
% 0.20/0.53    v1_relat_1(sK7(sK0,sK1,sK2)) | ~spl8_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f308])).
% 0.20/0.53  fof(f305,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | ~v1_relat_1(sK2) | (~spl8_5 | ~spl8_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f296,f261])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK2) | ~spl8_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f259])).
% 0.20/0.53  fof(f296,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_relat_1(sK2) | ~spl8_5),
% 0.20/0.53    inference(resolution,[],[f153,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.53  fof(f349,plain,(
% 0.20/0.53    v1_partfun1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | v1_xboole_0(k2_relat_1(sK2)) | (~spl8_5 | ~spl8_15)),
% 0.20/0.53    inference(subsumption_resolution,[],[f348,f153])).
% 0.20/0.53  fof(f348,plain,(
% 0.20/0.53    v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | v1_xboole_0(k2_relat_1(sK2)) | ~spl8_15),
% 0.20/0.53    inference(resolution,[],[f346,f70])).
% 0.20/0.53  fof(f346,plain,(
% 0.20/0.53    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | ~spl8_15),
% 0.20/0.53    inference(avatar_component_clause,[],[f344])).
% 0.20/0.53  fof(f535,plain,(
% 0.20/0.53    ~spl8_23 | ~spl8_5 | spl8_6 | ~spl8_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f525,f160,f156,f152,f532])).
% 0.20/0.53  fof(f532,plain,(
% 0.20/0.53    spl8_23 <=> v1_partfun1(sK2,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.20/0.53  fof(f524,plain,(
% 0.20/0.53    spl8_7 | ~spl8_10 | ~spl8_11 | ~spl8_14),
% 0.20/0.53    inference(avatar_split_clause,[],[f340,f323,f259,f247,f160])).
% 0.20/0.53  fof(f247,plain,(
% 0.20/0.53    spl8_10 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.53  fof(f323,plain,(
% 0.20/0.53    spl8_14 <=> v1_relat_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.53  fof(f340,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl8_10 | ~spl8_11 | ~spl8_14)),
% 0.20/0.53    inference(forward_demodulation,[],[f333,f261])).
% 0.20/0.53  fof(f333,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl8_10 | ~spl8_14)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f249,f102,f325,f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.53  fof(f325,plain,(
% 0.20/0.53    v1_relat_1(sK2) | ~spl8_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f323])).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK2),sK1) | ~spl8_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f247])).
% 0.20/0.53  fof(f398,plain,(
% 0.20/0.53    ~spl8_19 | spl8_20 | ~spl8_1 | ~spl8_3 | ~spl8_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f228,f165,f133,f123,f396,f392])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    spl8_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    spl8_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    spl8_8 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.53  fof(f228,plain,(
% 0.20/0.53    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0)) ) | (~spl8_1 | ~spl8_3 | ~spl8_8)),
% 0.20/0.53    inference(subsumption_resolution,[],[f227,f167])).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    v1_relat_1(k1_xboole_0) | ~spl8_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f165])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl8_1 | ~spl8_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f226,f145])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_1),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f125,f66])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0) | ~spl8_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f123])).
% 0.20/0.53  fof(f226,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0,X0,k1_xboole_0),k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl8_3),
% 0.20/0.53    inference(superposition,[],[f109,f135])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl8_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f133])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    ( ! [X2,X1] : (r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | v1_funct_2(X2,k1_relat_1(X2),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(equality_resolution,[],[f86])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK4(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.20/0.53  fof(f373,plain,(
% 0.20/0.53    spl8_18 | ~spl8_2 | ~spl8_5 | ~spl8_11 | ~spl8_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f320,f308,f259,f152,f128,f370])).
% 0.20/0.53  fof(f360,plain,(
% 0.20/0.53    spl8_17 | ~spl8_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f182,f128,f357])).
% 0.20/0.53  fof(f357,plain,(
% 0.20/0.53    spl8_17 <=> sK2 = sK7(sK0,sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.53  % (478)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  fof(f347,plain,(
% 0.20/0.53    spl8_15 | ~spl8_2 | ~spl8_5 | ~spl8_11 | ~spl8_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f321,f308,f259,f152,f128,f344])).
% 0.20/0.53  fof(f321,plain,(
% 0.20/0.53    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | (~spl8_2 | ~spl8_5 | ~spl8_11 | ~spl8_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f306,f312])).
% 0.20/0.53  fof(f306,plain,(
% 0.20/0.53    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl8_5 | ~spl8_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f297,f261])).
% 0.20/0.53  fof(f297,plain,(
% 0.20/0.53    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl8_5),
% 0.20/0.53    inference(resolution,[],[f153,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f25])).
% 0.20/0.53  fof(f326,plain,(
% 0.20/0.53    spl8_14 | ~spl8_2 | ~spl8_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f312,f308,f128,f323])).
% 0.20/0.53  % (458)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.53  fof(f311,plain,(
% 0.20/0.53    spl8_13 | ~spl8_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f179,f128,f308])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    v1_relat_1(sK7(sK0,sK1,sK2)) | ~spl8_2),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f130,f120])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    ( ! [X6,X0,X1] : (v1_relat_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f54])).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    spl8_5 | ~spl8_2 | ~spl8_12),
% 0.20/0.53    inference(avatar_split_clause,[],[f286,f282,f128,f152])).
% 0.20/0.53  fof(f282,plain,(
% 0.20/0.53    spl8_12 <=> v1_funct_1(sK7(sK0,sK1,sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.53  fof(f286,plain,(
% 0.20/0.53    v1_funct_1(sK2) | (~spl8_2 | ~spl8_12)),
% 0.20/0.53    inference(forward_demodulation,[],[f284,f182])).
% 0.20/0.53  fof(f284,plain,(
% 0.20/0.53    v1_funct_1(sK7(sK0,sK1,sK2)) | ~spl8_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f282])).
% 0.20/0.53  fof(f285,plain,(
% 0.20/0.53    spl8_12 | ~spl8_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f176,f128,f282])).
% 0.20/0.53  fof(f176,plain,(
% 0.20/0.53    v1_funct_1(sK7(sK0,sK1,sK2)) | ~spl8_2),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f130,f119])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    ( ! [X6,X0,X1] : (v1_funct_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f91])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK7(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f54])).
% 0.20/0.53  % (456)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    spl8_11 | ~spl8_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f203,f128,f259])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK2) | ~spl8_2),
% 0.20/0.53    inference(forward_demodulation,[],[f200,f182])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    sK0 = k1_relat_1(sK7(sK0,sK1,sK2)) | ~spl8_2),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f130,f117])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_funct_2(X0,X1)) | k1_relat_1(sK7(X0,X1,X6)) = X0) )),
% 0.20/0.53    inference(equality_resolution,[],[f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK7(X0,X1,X6)) = X0 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f54])).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    spl8_10 | ~spl8_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f198,f128,f247])).
% 0.20/0.53  fof(f198,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK2),sK1) | ~spl8_2),
% 0.20/0.53    inference(forward_demodulation,[],[f195,f182])).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK7(sK0,sK1,sK2)),sK1) | ~spl8_2),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f130,f116])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_funct_2(X0,X1)) | r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK7(X0,X1,X6)),X1) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.20/0.53    inference(cnf_transformation,[],[f54])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    spl8_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f147,f165])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    v1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(superposition,[],[f68,f104])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f46])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    ~spl8_5 | ~spl8_6 | ~spl8_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f56,f160,f156,f152])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.53    inference(negated_conjecture,[],[f18])).
% 0.20/0.53  fof(f18,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    spl8_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f58,f133])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    spl8_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f55,f128])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    spl8_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f57,f123])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (483)------------------------------
% 0.20/0.53  % (483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (483)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (483)Memory used [KB]: 11897
% 0.20/0.53  % (483)Time elapsed: 0.121 s
% 0.20/0.53  % (483)------------------------------
% 0.20/0.53  % (483)------------------------------
% 0.20/0.54  % (454)Success in time 0.185 s
%------------------------------------------------------------------------------
