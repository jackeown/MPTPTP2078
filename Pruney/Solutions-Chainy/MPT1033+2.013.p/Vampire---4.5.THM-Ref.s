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
% DateTime   : Thu Dec  3 13:06:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 226 expanded)
%              Number of leaves         :   31 (  90 expanded)
%              Depth                    :    8
%              Number of atoms          :  390 ( 877 expanded)
%              Number of equality atoms :   50 ( 146 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f496,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f80,f85,f90,f104,f110,f116,f138,f217,f218,f233,f251,f290,f346,f358,f413,f416,f495])).

fof(f495,plain,
    ( spl6_23
    | ~ spl6_13
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f493,f319,f113,f206])).

fof(f206,plain,
    ( spl6_23
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f113,plain,
    ( spl6_13
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f319,plain,
    ( spl6_37
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f493,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_13
    | ~ spl6_37 ),
    inference(resolution,[],[f320,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f139,f49])).

fof(f49,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = X0 )
    | ~ spl6_13 ),
    inference(resolution,[],[f120,f115])).

fof(f115,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f39,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f320,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f319])).

fof(f416,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK3
    | sK2 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f413,plain,
    ( spl6_17
    | ~ spl6_13
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f412,f315,f113,f177])).

fof(f177,plain,
    ( spl6_17
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f315,plain,
    ( spl6_36
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f412,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_13
    | ~ spl6_36 ),
    inference(resolution,[],[f316,f141])).

fof(f316,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f315])).

fof(f358,plain,
    ( spl6_37
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f357,f96,f77,f319])).

fof(f77,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f96,plain,
    ( spl6_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f357,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f341,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f341,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f79,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f79,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f346,plain,
    ( spl6_36
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f345,f96,f52,f315])).

fof(f52,plain,
    ( spl6_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f345,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f338,f48])).

fof(f338,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f54,f97])).

fof(f54,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f290,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | spl6_10
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | spl6_10
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f98,f98,f59,f84,f54,f79,f54,f79,f277])).

fof(f277,plain,
    ( ! [X14,X17,X15,X16] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X16)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X14,X17)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | k1_xboole_0 = X15
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X17)))
        | ~ v1_funct_2(sK3,X14,X16)
        | ~ v1_funct_2(sK2,X14,X15)
        | k1_xboole_0 = X16 )
    | ~ spl6_29 ),
    inference(resolution,[],[f250,f37])).

fof(f250,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(X3)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_2(sK3,X0,X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl6_29
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_xboole_0(X3)
        | ~ v1_funct_2(sK3,X0,X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f84,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f59,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f98,plain,
    ( k1_xboole_0 != sK1
    | spl6_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f251,plain,
    ( ~ spl6_8
    | spl6_29
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f247,f231,f249,f87])).

fof(f87,plain,
    ( spl6_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f231,plain,
    ( spl6_27
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X2)
        | ~ v1_funct_2(sK2,X0,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f247,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,X0,X3)
        | v1_xboole_0(X3) )
    | ~ spl6_27 ),
    inference(resolution,[],[f246,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f246,plain,
    ( ! [X14,X12,X13] :
        ( ~ v1_partfun1(sK3,X12)
        | ~ v1_funct_2(sK2,X12,X14)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X12,X14)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | k1_xboole_0 = X14 )
    | ~ spl6_27 ),
    inference(resolution,[],[f232,f37])).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK3,X0) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f231])).

fof(f233,plain,
    ( ~ spl6_3
    | spl6_27
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f229,f197,f231,f62])).

fof(f62,plain,
    ( spl6_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f197,plain,
    ( spl6_22
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_partfun1(sK2,X4)
        | ~ v1_partfun1(sK3,X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f229,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK3,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,X0,X2)
        | v1_xboole_0(X2) )
    | ~ spl6_22 ),
    inference(resolution,[],[f198,f38])).

fof(f198,plain,
    ( ! [X4,X5] :
        ( ~ v1_partfun1(sK2,X4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_partfun1(sK3,X4)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f197])).

fof(f218,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f217,plain,
    ( spl6_20
    | ~ spl6_5
    | spl6_22
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f201,f87,f62,f197,f72,f189])).

fof(f189,plain,
    ( spl6_20
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f72,plain,
    ( spl6_5
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f201,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_partfun1(sK2,X2)
        | ~ v1_partfun1(sK3,X2)
        | ~ r1_partfun1(sK2,sK3)
        | sK2 = sK3 )
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(resolution,[],[f163,f64])).

fof(f64,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f163,plain,
    ( ! [X6,X8,X7] :
        ( ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_partfun1(X6,X7)
        | ~ v1_partfun1(sK3,X7)
        | ~ r1_partfun1(X6,sK3)
        | sK3 = X6 )
    | ~ spl6_8 ),
    inference(resolution,[],[f45,f89])).

fof(f89,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_partfun1(X3,X0)
      | ~ r1_partfun1(X2,X3)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f138,plain,
    ( spl6_15
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f124,f77,f135])).

fof(f135,plain,
    ( spl6_15
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f124,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl6_6 ),
    inference(resolution,[],[f50,f79])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f116,plain,
    ( spl6_13
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f111,f107,f101,f113])).

fof(f101,plain,
    ( spl6_11
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f107,plain,
    ( spl6_12
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f111,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(backward_demodulation,[],[f103,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK5
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f103,plain,
    ( v1_xboole_0(sK5)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f110,plain,
    ( spl6_12
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f105,f101,f107])).

fof(f105,plain,
    ( k1_xboole_0 = sK5
    | ~ spl6_11 ),
    inference(resolution,[],[f37,f103])).

fof(f104,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f47,f101])).

fof(f47,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f90,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f28,f87])).

fof(f28,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f85,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f29,f82])).

fof(f29,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f30,f77])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f32,f67])).

fof(f67,plain,
    ( spl6_4
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f32,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f34,f57])).

fof(f34,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f35,f52])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:15:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.46  % (31170)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.46  % (31178)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.47  % (31170)Refutation not found, incomplete strategy% (31170)------------------------------
% 0.21/0.47  % (31170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (31170)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (31170)Memory used [KB]: 1663
% 0.21/0.47  % (31170)Time elapsed: 0.065 s
% 0.21/0.47  % (31170)------------------------------
% 0.21/0.47  % (31170)------------------------------
% 0.21/0.48  % (31178)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f496,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f75,f80,f85,f90,f104,f110,f116,f138,f217,f218,f233,f251,f290,f346,f358,f413,f416,f495])).
% 0.21/0.48  fof(f495,plain,(
% 0.21/0.48    spl6_23 | ~spl6_13 | ~spl6_37),
% 0.21/0.48    inference(avatar_split_clause,[],[f493,f319,f113,f206])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    spl6_23 <=> k1_xboole_0 = sK3),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl6_13 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    spl6_37 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.48  fof(f493,plain,(
% 0.21/0.48    k1_xboole_0 = sK3 | (~spl6_13 | ~spl6_37)),
% 0.21/0.48    inference(resolution,[],[f320,f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl6_13),
% 0.21/0.48    inference(forward_demodulation,[],[f139,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = X0) ) | ~spl6_13),
% 0.21/0.48    inference(resolution,[],[f120,f115])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | ~spl6_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f113])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(resolution,[],[f39,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_37),
% 0.21/0.48    inference(avatar_component_clause,[],[f319])).
% 0.21/0.48  fof(f416,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 | k1_xboole_0 != sK3 | sK2 = sK3),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f413,plain,(
% 0.21/0.48    spl6_17 | ~spl6_13 | ~spl6_36),
% 0.21/0.48    inference(avatar_split_clause,[],[f412,f315,f113,f177])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    spl6_17 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.48  fof(f315,plain,(
% 0.21/0.48    spl6_36 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.48  fof(f412,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | (~spl6_13 | ~spl6_36)),
% 0.21/0.48    inference(resolution,[],[f316,f141])).
% 0.21/0.48  fof(f316,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_36),
% 0.21/0.48    inference(avatar_component_clause,[],[f315])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    spl6_37 | ~spl6_6 | ~spl6_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f357,f96,f77,f319])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl6_10 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.48  fof(f357,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl6_6 | ~spl6_10)),
% 0.21/0.48    inference(forward_demodulation,[],[f341,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f341,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_6 | ~spl6_10)),
% 0.21/0.48    inference(backward_demodulation,[],[f79,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl6_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f77])).
% 0.21/0.48  fof(f346,plain,(
% 0.21/0.48    spl6_36 | ~spl6_1 | ~spl6_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f345,f96,f52,f315])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl6_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_1 | ~spl6_10)),
% 0.21/0.48    inference(forward_demodulation,[],[f338,f48])).
% 0.21/0.48  fof(f338,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_1 | ~spl6_10)),
% 0.21/0.48    inference(backward_demodulation,[],[f54,f97])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    ~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_7 | spl6_10 | ~spl6_29),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f278])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    $false | (~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_7 | spl6_10 | ~spl6_29)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f98,f98,f59,f84,f54,f79,f54,f79,f277])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    ( ! [X14,X17,X15,X16] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X16))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X14,X17))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | k1_xboole_0 = X15 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X14,X17))) | ~v1_funct_2(sK3,X14,X16) | ~v1_funct_2(sK2,X14,X15) | k1_xboole_0 = X16) ) | ~spl6_29),
% 0.21/0.48    inference(resolution,[],[f250,f37])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X3) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_2(sK3,X0,X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | k1_xboole_0 = X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f249])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    spl6_29 <=> ! [X1,X3,X0,X2] : (~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X3) | ~v1_funct_2(sK3,X0,X3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | k1_xboole_0 = X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1) | ~spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl6_7 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1) | ~spl6_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl6_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | spl6_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ~spl6_8 | spl6_29 | ~spl6_27),
% 0.21/0.48    inference(avatar_split_clause,[],[f247,f231,f249,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl6_8 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    spl6_27 <=> ! [X1,X0,X2] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_funct_2(sK2,X0,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK3,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,X0,X3) | v1_xboole_0(X3)) ) | ~spl6_27),
% 0.21/0.48    inference(resolution,[],[f246,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ( ! [X14,X12,X13] : (~v1_partfun1(sK3,X12) | ~v1_funct_2(sK2,X12,X14) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X12,X14))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | k1_xboole_0 = X14) ) | ~spl6_27),
% 0.21/0.48    inference(resolution,[],[f232,f37])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK3,X0)) ) | ~spl6_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f231])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ~spl6_3 | spl6_27 | ~spl6_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f229,f197,f231,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl6_3 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    spl6_22 <=> ! [X5,X4] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_partfun1(sK2,X4) | ~v1_partfun1(sK3,X4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK3,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,X0,X2) | v1_xboole_0(X2)) ) | ~spl6_22),
% 0.21/0.48    inference(resolution,[],[f198,f38])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ( ! [X4,X5] : (~v1_partfun1(sK2,X4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_partfun1(sK3,X4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | ~spl6_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f197])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    spl6_20 | ~spl6_5 | spl6_22 | ~spl6_3 | ~spl6_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f201,f87,f62,f197,f72,f189])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    spl6_20 <=> sK2 = sK3),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl6_5 <=> r1_partfun1(sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_partfun1(sK2,X2) | ~v1_partfun1(sK3,X2) | ~r1_partfun1(sK2,sK3) | sK2 = sK3) ) | (~spl6_3 | ~spl6_8)),
% 0.21/0.48    inference(resolution,[],[f163,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f62])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ( ! [X6,X8,X7] : (~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~v1_partfun1(X6,X7) | ~v1_partfun1(sK3,X7) | ~r1_partfun1(X6,sK3) | sK3 = X6) ) | ~spl6_8),
% 0.21/0.48    inference(resolution,[],[f45,f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl6_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_partfun1(X3,X0) | ~r1_partfun1(X2,X3) | X2 = X3) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl6_15 | ~spl6_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f124,f77,f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl6_15 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl6_6),
% 0.21/0.48    inference(resolution,[],[f50,f79])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.21/0.48    inference(condensation,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl6_13 | ~spl6_11 | ~spl6_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f111,f107,f101,f113])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl6_11 <=> v1_xboole_0(sK5)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl6_12 <=> k1_xboole_0 = sK5),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | (~spl6_11 | ~spl6_12)),
% 0.21/0.48    inference(backward_demodulation,[],[f103,f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    k1_xboole_0 = sK5 | ~spl6_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    v1_xboole_0(sK5) | ~spl6_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl6_12 | ~spl6_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f105,f101,f107])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    k1_xboole_0 = sK5 | ~spl6_11),
% 0.21/0.48    inference(resolution,[],[f37,f103])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl6_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f101])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    v1_xboole_0(sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl6_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f87])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl6_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f82])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl6_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f77])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl6_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f72])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    r1_partfun1(sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl6_4 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f62])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl6_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f57])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl6_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f52])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (31178)------------------------------
% 0.21/0.48  % (31178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31178)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (31178)Memory used [KB]: 6524
% 0.21/0.48  % (31178)Time elapsed: 0.073 s
% 0.21/0.48  % (31178)------------------------------
% 0.21/0.48  % (31178)------------------------------
% 0.21/0.48  % (31162)Success in time 0.129 s
%------------------------------------------------------------------------------
