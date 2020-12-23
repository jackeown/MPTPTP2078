%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:50 EST 2020

% Result     : Theorem 19.47s
% Output     : Refutation 19.47s
% Verified   : 
% Statistics : Number of formulae       :  277 ( 609 expanded)
%              Number of leaves         :   57 ( 217 expanded)
%              Depth                    :   16
%              Number of atoms          : 1102 (3003 expanded)
%              Number of equality atoms :  201 ( 770 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41473,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f140,f144,f148,f213,f292,f294,f296,f298,f306,f333,f336,f621,f623,f647,f654,f716,f735,f870,f878,f903,f1063,f1183,f1377,f1383,f1419,f1467,f3528,f3550,f6176,f6180,f40365,f40867,f41150,f41378])).

fof(f41378,plain,(
    ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f41161])).

fof(f41161,plain,
    ( $false
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f65,f588])).

fof(f588,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f586])).

fof(f586,plain,
    ( spl4_17
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f65,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f41150,plain,
    ( ~ spl4_1
    | ~ spl4_90
    | ~ spl4_249
    | ~ spl4_485
    | ~ spl4_486
    | ~ spl4_3107 ),
    inference(avatar_contradiction_clause,[],[f41147])).

fof(f41147,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_90
    | ~ spl4_249
    | ~ spl4_485
    | ~ spl4_486
    | ~ spl4_3107 ),
    inference(unit_resulting_resolution,[],[f1376,f57,f126,f3523,f6036,f6040,f153,f41142,f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k2_funct_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(k2_funct_1(X0)),X1)
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f176,f80])).

fof(f80,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f176,plain,(
    ! [X2,X1] :
      ( ~ v4_relat_1(k2_funct_1(X1),X2)
      | ~ v1_relat_1(k2_funct_1(X1))
      | r1_tarski(k2_relat_1(X1),X2)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f89,f81])).

fof(f81,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f41142,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1)
    | ~ spl4_3107 ),
    inference(equality_resolution,[],[f40209])).

fof(f40209,plain,
    ( ! [X1] :
        ( k6_partfun1(X1) != k6_partfun1(sK1)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X1) )
    | ~ spl4_3107 ),
    inference(avatar_component_clause,[],[f40208])).

fof(f40208,plain,
    ( spl4_3107
  <=> ! [X1] :
        ( k6_partfun1(X1) != k6_partfun1(sK1)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3107])])).

fof(f153,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f91,f59])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f6040,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl4_486 ),
    inference(avatar_component_clause,[],[f6039])).

fof(f6039,plain,
    ( spl4_486
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_486])])).

fof(f6036,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_485 ),
    inference(avatar_component_clause,[],[f6035])).

fof(f6035,plain,
    ( spl4_485
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_485])])).

fof(f3523,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_249 ),
    inference(avatar_component_clause,[],[f3522])).

fof(f3522,plain,
    ( spl4_249
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_249])])).

fof(f126,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f1376,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_90 ),
    inference(avatar_component_clause,[],[f1374])).

fof(f1374,plain,
    ( spl4_90
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f40867,plain,
    ( ~ spl4_1
    | ~ spl4_90
    | ~ spl4_20
    | spl4_17
    | ~ spl4_3106 ),
    inference(avatar_split_clause,[],[f40377,f40204,f586,f607,f1374,f124])).

fof(f607,plain,
    ( spl4_20
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f40204,plain,
    ( spl4_3106
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3106])])).

fof(f40377,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3106 ),
    inference(superposition,[],[f80,f40206])).

fof(f40206,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_3106 ),
    inference(avatar_component_clause,[],[f40204])).

fof(f40365,plain,
    ( ~ spl4_3
    | spl4_3106
    | spl4_3107
    | ~ spl4_34
    | ~ spl4_52
    | ~ spl4_250 ),
    inference(avatar_split_clause,[],[f40364,f3526,f900,f730,f40208,f40204,f133])).

fof(f133,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f730,plain,
    ( spl4_34
  <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f900,plain,
    ( spl4_52
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f3526,plain,
    ( spl4_250
  <=> ! [X49,X50] :
        ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(X49))
        | k2_funct_1(sK3) = X49
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X50)
        | k6_partfun1(X50) != k5_relat_1(k2_funct_1(sK2),X49)
        | ~ v1_relat_1(X49) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_250])])).

fof(f40364,plain,
    ( ! [X22] :
        ( k6_partfun1(sK1) != k6_partfun1(X22)
        | sK2 = k2_funct_1(sK3)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X22)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_34
    | ~ spl4_52
    | ~ spl4_250 ),
    inference(trivial_inequality_removal,[],[f40363])).

fof(f40363,plain,
    ( ! [X22] :
        ( k6_partfun1(sK0) != k6_partfun1(sK0)
        | k6_partfun1(sK1) != k6_partfun1(X22)
        | sK2 = k2_funct_1(sK3)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X22)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_34
    | ~ spl4_52
    | ~ spl4_250 ),
    inference(forward_demodulation,[],[f40195,f732])).

fof(f732,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f730])).

fof(f40195,plain,
    ( ! [X22] :
        ( k6_partfun1(sK1) != k6_partfun1(X22)
        | sK2 = k2_funct_1(sK3)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X22)
        | k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl4_52
    | ~ spl4_250 ),
    inference(superposition,[],[f3527,f902])).

fof(f902,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f900])).

fof(f3527,plain,
    ( ! [X50,X49] :
        ( k6_partfun1(X50) != k5_relat_1(k2_funct_1(sK2),X49)
        | k2_funct_1(sK3) = X49
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X50)
        | k6_partfun1(sK0) != k6_partfun1(k1_relat_1(X49))
        | ~ v1_relat_1(X49) )
    | ~ spl4_250 ),
    inference(avatar_component_clause,[],[f3526])).

fof(f6180,plain,
    ( ~ spl4_1
    | spl4_486 ),
    inference(avatar_contradiction_clause,[],[f6178])).

fof(f6178,plain,
    ( $false
    | ~ spl4_1
    | spl4_486 ),
    inference(unit_resulting_resolution,[],[f126,f57,f6041,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f6041,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_486 ),
    inference(avatar_component_clause,[],[f6039])).

fof(f6176,plain,
    ( ~ spl4_1
    | ~ spl4_90
    | spl4_485 ),
    inference(avatar_contradiction_clause,[],[f6173])).

fof(f6173,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_90
    | spl4_485 ),
    inference(unit_resulting_resolution,[],[f1376,f57,f126,f6037,f341])).

fof(f341,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f324,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f324,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f318,f79])).

fof(f318,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f317])).

fof(f317,plain,(
    ! [X0] :
      ( k6_partfun1(k2_relat_1(X0)) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,(
    ! [X0] :
      ( k6_partfun1(k2_relat_1(X0)) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f191,f81])).

fof(f191,plain,(
    ! [X2] :
      ( k6_partfun1(k2_relat_1(X2)) != k6_partfun1(k1_relat_1(k2_funct_1(X2)))
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k2_funct_1(X2))
      | v2_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X2] :
      ( k6_partfun1(k2_relat_1(X2)) != k6_partfun1(k1_relat_1(k2_funct_1(X2)))
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(k2_funct_1(X2))
      | v2_funct_1(k2_funct_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f114,f112])).

fof(f112,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f84,f69])).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(definition_unfolding,[],[f85,f69])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(f6037,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | spl4_485 ),
    inference(avatar_component_clause,[],[f6035])).

fof(f3550,plain,
    ( ~ spl4_1
    | spl4_249 ),
    inference(avatar_contradiction_clause,[],[f3548])).

fof(f3548,plain,
    ( $false
    | ~ spl4_1
    | spl4_249 ),
    inference(unit_resulting_resolution,[],[f126,f57,f3524,f78])).

fof(f3524,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_249 ),
    inference(avatar_component_clause,[],[f3522])).

fof(f3528,plain,
    ( ~ spl4_3
    | ~ spl4_90
    | ~ spl4_9
    | ~ spl4_20
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_249
    | ~ spl4_13
    | spl4_250
    | ~ spl4_23
    | ~ spl4_33
    | ~ spl4_92 ),
    inference(avatar_split_clause,[],[f3520,f1464,f725,f632,f3526,f330,f3522,f277,f124,f607,f281,f1374,f133])).

fof(f281,plain,
    ( spl4_9
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f277,plain,
    ( spl4_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f330,plain,
    ( spl4_13
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f632,plain,
    ( spl4_23
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f725,plain,
    ( spl4_33
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1464,plain,
    ( spl4_92
  <=> k6_partfun1(k2_relat_1(k2_funct_1(sK2))) = k2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f3520,plain,
    ( ! [X50,X49] :
        ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(X49))
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X49)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X50)
        | ~ v1_relat_1(k2_funct_1(sK3))
        | k6_partfun1(X50) != k5_relat_1(k2_funct_1(sK2),X49)
        | k2_funct_1(sK3) = X49
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v2_funct_1(sK2)
        | ~ v2_funct_1(sK3)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_23
    | ~ spl4_33
    | ~ spl4_92 ),
    inference(forward_demodulation,[],[f3413,f2018])).

fof(f2018,plain,
    ( k6_partfun1(sK0) = k2_funct_1(k6_partfun1(sK0))
    | ~ spl4_33
    | ~ spl4_92 ),
    inference(forward_demodulation,[],[f1466,f727])).

fof(f727,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f725])).

fof(f1466,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK2))) = k2_funct_1(k6_partfun1(sK0))
    | ~ spl4_92 ),
    inference(avatar_component_clause,[],[f1464])).

fof(f3413,plain,
    ( ! [X50,X49] :
        ( k2_funct_1(k6_partfun1(sK0)) != k6_partfun1(k1_relat_1(X49))
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X49)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK3)),X50)
        | ~ v1_relat_1(k2_funct_1(sK3))
        | k6_partfun1(X50) != k5_relat_1(k2_funct_1(sK2),X49)
        | k2_funct_1(sK3) = X49
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK3)
        | ~ v1_funct_1(sK3)
        | ~ v2_funct_1(sK2)
        | ~ v2_funct_1(sK3)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_23 ),
    inference(superposition,[],[f460,f634])).

fof(f634,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f632])).

fof(f460,plain,(
    ! [X24,X23,X21,X22] :
      ( k2_funct_1(k5_relat_1(X22,X21)) != k6_partfun1(k1_relat_1(X23))
      | ~ v1_relat_1(k2_funct_1(X22))
      | ~ v1_relat_1(X23)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(X21)),X24)
      | ~ v1_relat_1(k2_funct_1(X21))
      | k6_partfun1(X24) != k5_relat_1(k2_funct_1(X22),X23)
      | k2_funct_1(X21) = X23
      | ~ v1_funct_1(X22)
      | ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ v2_funct_1(X22)
      | ~ v2_funct_1(X21)
      | ~ v1_relat_1(X22) ) ),
    inference(superposition,[],[f115,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X2,X3) != k6_partfun1(X0)
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f90,f69,f69])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
      | k6_relat_1(X0) != k5_relat_1(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | ~ r1_tarski(k2_relat_1(X1),X0)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( X1 = X3
              | k6_relat_1(X0) != k5_relat_1(X2,X3)
              | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
              | ~ r1_tarski(k2_relat_1(X1),X0)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & r1_tarski(k2_relat_1(X1),X0) )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_relat_1)).

fof(f1467,plain,
    ( ~ spl4_3
    | ~ spl4_9
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_12
    | ~ spl4_7
    | spl4_92
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f1428,f709,f1464,f273,f326,f330,f277,f281,f133])).

fof(f326,plain,
    ( spl4_12
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f273,plain,
    ( spl4_7
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f709,plain,
    ( spl4_31
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f1428,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK2))) = k2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_31 ),
    inference(superposition,[],[f238,f711])).

fof(f711,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f709])).

fof(f238,plain,(
    ! [X1] :
      ( k2_funct_1(k5_relat_1(X1,k2_funct_1(X1))) = k6_partfun1(k2_relat_1(k2_funct_1(X1)))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v2_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,(
    ! [X1] :
      ( k2_funct_1(k5_relat_1(X1,k2_funct_1(X1))) = k6_partfun1(k2_relat_1(k2_funct_1(X1)))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v2_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f112,f86])).

fof(f1419,plain,(
    ~ spl4_89 ),
    inference(avatar_contradiction_clause,[],[f1384])).

fof(f1384,plain,
    ( $false
    | ~ spl4_89 ),
    inference(subsumption_resolution,[],[f63,f1372])).

fof(f1372,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_89 ),
    inference(avatar_component_clause,[],[f1370])).

fof(f1370,plain,
    ( spl4_89
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f63,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f1383,plain,(
    spl4_88 ),
    inference(avatar_contradiction_clause,[],[f1382])).

fof(f1382,plain,
    ( $false
    | spl4_88 ),
    inference(subsumption_resolution,[],[f58,f1368])).

fof(f1368,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_88 ),
    inference(avatar_component_clause,[],[f1366])).

fof(f1366,plain,
    ( spl4_88
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f1377,plain,
    ( ~ spl4_88
    | ~ spl4_19
    | ~ spl4_20
    | spl4_89
    | spl4_90
    | ~ spl4_43
    | ~ spl4_6
    | ~ spl4_76 ),
    inference(avatar_split_clause,[],[f1362,f1181,f210,f804,f1374,f1370,f607,f603,f1366])).

fof(f603,plain,
    ( spl4_19
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f804,plain,
    ( spl4_43
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f210,plain,
    ( spl4_6
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1181,plain,
    ( spl4_76
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f1362,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_6
    | ~ spl4_76 ),
    inference(superposition,[],[f1182,f212])).

fof(f212,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f210])).

fof(f1182,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f1181])).

fof(f1183,plain,
    ( ~ spl4_8
    | spl4_76
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f1179,f289,f285,f1181,f277])).

fof(f285,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f289,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1179,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f1178])).

fof(f1178,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(superposition,[],[f101,f60])).

fof(f60,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f1063,plain,
    ( ~ spl4_3
    | ~ spl4_9
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_12
    | ~ spl4_7
    | spl4_33
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f1058,f709,f725,f273,f326,f330,f277,f281,f133])).

fof(f1058,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_31 ),
    inference(superposition,[],[f180,f711])).

fof(f180,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k2_relat_1(k2_funct_1(X0)))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f112,f80])).

fof(f903,plain,
    ( spl4_52
    | spl4_32
    | ~ spl4_9
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f898,f289,f285,f277,f281,f713,f900])).

fof(f713,plain,
    ( spl4_32
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f898,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(trivial_inequality_removal,[],[f897])).

fof(f897,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(superposition,[],[f97,f60])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f878,plain,(
    spl4_43 ),
    inference(avatar_contradiction_clause,[],[f873])).

fof(f873,plain,
    ( $false
    | spl4_43 ),
    inference(unit_resulting_resolution,[],[f107,f108,f806,f195])).

fof(f195,plain,(
    ! [X1] :
      ( ~ v1_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1))
      | v2_funct_1(k6_partfun1(X1)) ) ),
    inference(trivial_inequality_removal,[],[f194])).

fof(f194,plain,(
    ! [X1] :
      ( k6_partfun1(X1) != k6_partfun1(X1)
      | ~ v1_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1))
      | v2_funct_1(k6_partfun1(X1)) ) ),
    inference(forward_demodulation,[],[f192,f110])).

fof(f110,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f74,f69])).

fof(f74,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f192,plain,(
    ! [X1] :
      ( k6_partfun1(X1) != k6_partfun1(k1_relat_1(k6_partfun1(X1)))
      | ~ v1_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1))
      | v2_funct_1(k6_partfun1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X1] :
      ( k6_partfun1(X1) != k6_partfun1(k1_relat_1(k6_partfun1(X1)))
      | ~ v1_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1))
      | ~ v1_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1))
      | v2_funct_1(k6_partfun1(X1))
      | ~ v1_relat_1(k6_partfun1(X1)) ) ),
    inference(superposition,[],[f114,f159])).

fof(f159,plain,(
    ! [X0] :
      ( k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X0))
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f111,f109])).

fof(f109,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f75,f69])).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f111,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f76,f69])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f806,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_43 ),
    inference(avatar_component_clause,[],[f804])).

fof(f108,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f70,f69])).

fof(f70,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f107,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f71,f69])).

fof(f71,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f870,plain,(
    ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f849])).

fof(f849,plain,
    ( $false
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f64,f715])).

fof(f715,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f713])).

fof(f64,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f735,plain,
    ( ~ spl4_3
    | ~ spl4_9
    | ~ spl4_8
    | spl4_34
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f721,f709,f730,f277,f281,f133])).

fof(f721,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_31 ),
    inference(superposition,[],[f113,f711])).

fof(f113,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f83,f69])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f716,plain,
    ( spl4_31
    | spl4_32
    | ~ spl4_9
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f707,f289,f285,f277,f281,f713,f709])).

fof(f707,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f706])).

fof(f706,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f96,f60])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f654,plain,
    ( ~ spl4_8
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_10
    | spl4_23
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f651,f210,f632,f285,f607,f603,f277])).

fof(f651,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f104,f212])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f647,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f636])).

fof(f636,plain,
    ( $false
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f66,f57,f59,f68,f208,f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f208,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl4_5
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f623,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f622])).

fof(f622,plain,
    ( $false
    | spl4_20 ),
    inference(subsumption_resolution,[],[f57,f609])).

fof(f609,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f607])).

fof(f621,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f620])).

fof(f620,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f59,f605])).

fof(f605,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f603])).

fof(f336,plain,
    ( ~ spl4_3
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | ~ spl4_3
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f135,f66,f332,f78])).

fof(f332,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f330])).

fof(f135,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f333,plain,
    ( ~ spl4_9
    | spl4_12
    | ~ spl4_13
    | ~ spl4_8
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f321,f273,f133,f277,f330,f326,f281])).

fof(f321,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl4_7 ),
    inference(resolution,[],[f318,f275])).

fof(f275,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f273])).

fof(f306,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f67,f291])).

fof(f291,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f289])).

fof(f67,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f298,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f68,f287])).

fof(f287,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f285])).

fof(f296,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f62,f283])).

fof(f283,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f281])).

fof(f62,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f294,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f66,f279])).

fof(f279,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f277])).

fof(f292,plain,
    ( spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f271,f289,f285,f281,f277,f273])).

fof(f271,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f270])).

fof(f270,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f93,f60])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f213,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f203,f210,f206])).

fof(f203,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f200,f61])).

fof(f61,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f200,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f103,f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f148,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f87,f139])).

fof(f139,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f87,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f144,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f87,f130])).

fof(f130,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f140,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f121,f137,f133])).

fof(f121,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f77,f68])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f131,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f120,f128,f124])).

fof(f120,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f77,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:44:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (20398)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (20402)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.48  % (20420)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.48  % (20409)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.49  % (20409)Refutation not found, incomplete strategy% (20409)------------------------------
% 0.20/0.49  % (20409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (20412)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.49  % (20409)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (20409)Memory used [KB]: 10746
% 0.20/0.49  % (20409)Time elapsed: 0.086 s
% 0.20/0.49  % (20409)------------------------------
% 0.20/0.49  % (20409)------------------------------
% 0.20/0.49  % (20406)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (20397)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (20394)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (20395)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (20396)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (20419)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (20411)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (20407)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (20415)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (20414)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (20401)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (20393)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (20405)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (20408)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (20403)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (20404)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (20400)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (20416)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (20418)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (20399)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (20422)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (20421)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (20417)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (20410)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (20413)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.88/0.61  % (20423)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.27/0.80  % (20417)Time limit reached!
% 3.27/0.80  % (20417)------------------------------
% 3.27/0.80  % (20417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.80  % (20417)Termination reason: Time limit
% 3.27/0.80  
% 3.27/0.80  % (20417)Memory used [KB]: 12792
% 3.27/0.80  % (20417)Time elapsed: 0.400 s
% 3.27/0.80  % (20417)------------------------------
% 3.27/0.80  % (20417)------------------------------
% 3.27/0.81  % (20395)Time limit reached!
% 3.27/0.81  % (20395)------------------------------
% 3.27/0.81  % (20395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.81  % (20395)Termination reason: Time limit
% 3.27/0.81  
% 3.27/0.81  % (20395)Memory used [KB]: 7036
% 3.27/0.81  % (20395)Time elapsed: 0.411 s
% 3.27/0.81  % (20395)------------------------------
% 3.27/0.81  % (20395)------------------------------
% 4.13/0.89  % (20422)Time limit reached!
% 4.13/0.89  % (20422)------------------------------
% 4.13/0.89  % (20422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.13/0.89  % (20422)Termination reason: Time limit
% 4.13/0.89  % (20422)Termination phase: Saturation
% 4.13/0.89  
% 4.13/0.89  % (20422)Memory used [KB]: 4221
% 4.13/0.89  % (20422)Time elapsed: 0.500 s
% 4.13/0.89  % (20422)------------------------------
% 4.13/0.89  % (20422)------------------------------
% 4.37/0.93  % (20407)Time limit reached!
% 4.37/0.93  % (20407)------------------------------
% 4.37/0.93  % (20407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.93  % (20407)Termination reason: Time limit
% 4.37/0.93  
% 4.37/0.93  % (20407)Memory used [KB]: 6012
% 4.37/0.93  % (20407)Time elapsed: 0.504 s
% 4.37/0.93  % (20407)------------------------------
% 4.37/0.93  % (20407)------------------------------
% 4.37/0.95  % (20425)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.37/0.96  % (20399)Time limit reached!
% 4.37/0.96  % (20399)------------------------------
% 4.37/0.96  % (20399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.96  % (20399)Termination reason: Time limit
% 4.37/0.96  % (20399)Termination phase: Saturation
% 4.37/0.96  
% 4.37/0.96  % (20399)Memory used [KB]: 14583
% 4.37/0.96  % (20399)Time elapsed: 0.500 s
% 4.37/0.96  % (20399)------------------------------
% 4.37/0.96  % (20399)------------------------------
% 4.37/0.97  % (20424)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.95/1.02  % (20400)Time limit reached!
% 4.95/1.02  % (20400)------------------------------
% 4.95/1.02  % (20400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.95/1.02  % (20400)Termination reason: Time limit
% 4.95/1.02  % (20400)Termination phase: Saturation
% 4.95/1.02  
% 4.95/1.02  % (20400)Memory used [KB]: 6140
% 4.95/1.02  % (20400)Time elapsed: 0.600 s
% 4.95/1.02  % (20400)------------------------------
% 4.95/1.02  % (20400)------------------------------
% 4.95/1.02  % (20426)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.95/1.05  % (20427)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.47/1.09  % (20428)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.47/1.16  % (20429)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.85/1.23  % (20394)Time limit reached!
% 6.85/1.23  % (20394)------------------------------
% 6.85/1.23  % (20394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.85/1.23  % (20394)Termination reason: Time limit
% 6.85/1.23  
% 6.85/1.23  % (20394)Memory used [KB]: 6268
% 6.85/1.23  % (20394)Time elapsed: 0.828 s
% 6.85/1.23  % (20394)------------------------------
% 6.85/1.23  % (20394)------------------------------
% 6.85/1.30  % (20396)Time limit reached!
% 6.85/1.30  % (20396)------------------------------
% 6.85/1.30  % (20396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.85/1.30  % (20396)Termination reason: Time limit
% 6.85/1.30  % (20396)Termination phase: Saturation
% 6.85/1.30  
% 6.85/1.30  % (20396)Memory used [KB]: 7547
% 6.85/1.30  % (20396)Time elapsed: 0.900 s
% 6.85/1.30  % (20396)------------------------------
% 6.85/1.30  % (20396)------------------------------
% 7.64/1.33  % (20431)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 8.13/1.40  % (20420)Time limit reached!
% 8.13/1.40  % (20420)------------------------------
% 8.13/1.40  % (20420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.13/1.40  % (20420)Termination reason: Time limit
% 8.13/1.40  
% 8.13/1.40  % (20420)Memory used [KB]: 13048
% 8.13/1.40  % (20420)Time elapsed: 1.018 s
% 8.13/1.40  % (20420)------------------------------
% 8.13/1.40  % (20420)------------------------------
% 8.13/1.42  % (20405)Time limit reached!
% 8.13/1.42  % (20405)------------------------------
% 8.13/1.42  % (20405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.13/1.42  % (20405)Termination reason: Time limit
% 8.13/1.42  
% 8.13/1.42  % (20405)Memory used [KB]: 16502
% 8.13/1.42  % (20405)Time elapsed: 1.006 s
% 8.13/1.42  % (20405)------------------------------
% 8.13/1.42  % (20405)------------------------------
% 8.13/1.44  % (20432)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 9.08/1.54  % (20433)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.08/1.56  % (20434)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.08/1.61  % (20393)Time limit reached!
% 9.08/1.61  % (20393)------------------------------
% 9.08/1.61  % (20393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.08/1.61  % (20393)Termination reason: Time limit
% 9.08/1.61  
% 9.08/1.61  % (20393)Memory used [KB]: 4221
% 9.08/1.61  % (20393)Time elapsed: 1.209 s
% 9.08/1.61  % (20393)------------------------------
% 9.08/1.61  % (20393)------------------------------
% 9.78/1.65  % (20429)Time limit reached!
% 9.78/1.65  % (20429)------------------------------
% 9.78/1.65  % (20429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.78/1.65  % (20429)Termination reason: Time limit
% 9.78/1.65  
% 9.78/1.65  % (20429)Memory used [KB]: 17526
% 9.78/1.65  % (20429)Time elapsed: 0.605 s
% 9.78/1.65  % (20429)------------------------------
% 9.78/1.65  % (20429)------------------------------
% 9.78/1.66  % (20425)Time limit reached!
% 9.78/1.66  % (20425)------------------------------
% 9.78/1.66  % (20425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.78/1.66  % (20425)Termination reason: Time limit
% 9.78/1.66  % (20425)Termination phase: Saturation
% 9.78/1.66  
% 9.78/1.66  % (20425)Memory used [KB]: 13688
% 9.78/1.66  % (20425)Time elapsed: 0.800 s
% 9.78/1.66  % (20425)------------------------------
% 9.78/1.66  % (20425)------------------------------
% 10.25/1.71  % (20398)Time limit reached!
% 10.25/1.71  % (20398)------------------------------
% 10.25/1.71  % (20398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.25/1.71  % (20398)Termination reason: Time limit
% 10.25/1.71  % (20398)Termination phase: Saturation
% 10.25/1.71  
% 10.25/1.71  % (20398)Memory used [KB]: 8827
% 10.25/1.71  % (20398)Time elapsed: 1.323 s
% 10.25/1.71  % (20398)------------------------------
% 10.25/1.71  % (20398)------------------------------
% 10.25/1.77  % (20435)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 11.26/1.79  % (20436)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 11.26/1.81  % (20437)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.61/1.85  % (20438)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 12.86/2.02  % (20419)Time limit reached!
% 12.86/2.02  % (20419)------------------------------
% 12.86/2.02  % (20419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.86/2.02  % (20419)Termination reason: Time limit
% 12.86/2.02  
% 12.86/2.02  % (20419)Memory used [KB]: 13688
% 12.86/2.02  % (20419)Time elapsed: 1.625 s
% 12.86/2.02  % (20419)------------------------------
% 12.86/2.02  % (20419)------------------------------
% 13.88/2.11  % (20437)Time limit reached!
% 13.88/2.11  % (20437)------------------------------
% 13.88/2.11  % (20437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.88/2.11  % (20437)Termination reason: Time limit
% 13.88/2.11  % (20437)Termination phase: Saturation
% 13.88/2.11  
% 13.88/2.11  % (20437)Memory used [KB]: 14456
% 13.88/2.11  % (20437)Time elapsed: 0.400 s
% 13.88/2.11  % (20437)------------------------------
% 13.88/2.11  % (20437)------------------------------
% 14.02/2.18  % (20439)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 14.62/2.23  % (20433)Time limit reached!
% 14.62/2.23  % (20433)------------------------------
% 14.62/2.23  % (20433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.62/2.23  % (20433)Termination reason: Time limit
% 14.62/2.23  
% 14.62/2.24  % (20433)Memory used [KB]: 17398
% 14.62/2.24  % (20433)Time elapsed: 0.816 s
% 14.62/2.24  % (20433)------------------------------
% 14.62/2.24  % (20433)------------------------------
% 14.62/2.24  % (20440)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 14.62/2.25  % (20413)Time limit reached!
% 14.62/2.25  % (20413)------------------------------
% 14.62/2.25  % (20413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.62/2.25  % (20413)Termination reason: Time limit
% 14.62/2.25  
% 14.62/2.25  % (20413)Memory used [KB]: 26225
% 14.62/2.25  % (20413)Time elapsed: 1.840 s
% 14.62/2.25  % (20413)------------------------------
% 14.62/2.25  % (20413)------------------------------
% 16.02/2.38  % (20441)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 16.09/2.40  % (20442)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 16.34/2.46  % (20439)Time limit reached!
% 16.34/2.46  % (20439)------------------------------
% 16.34/2.46  % (20439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.34/2.46  % (20439)Termination reason: Time limit
% 16.34/2.46  
% 16.34/2.46  % (20439)Memory used [KB]: 7036
% 16.34/2.46  % (20439)Time elapsed: 0.423 s
% 16.34/2.46  % (20439)------------------------------
% 16.34/2.46  % (20439)------------------------------
% 17.62/2.61  % (20443)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 17.62/2.63  % (20440)Time limit reached!
% 17.62/2.63  % (20440)------------------------------
% 17.62/2.63  % (20440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.62/2.63  % (20440)Termination reason: Time limit
% 17.62/2.63  
% 17.62/2.63  % (20440)Memory used [KB]: 11769
% 17.62/2.63  % (20440)Time elapsed: 0.505 s
% 17.62/2.63  % (20440)------------------------------
% 17.62/2.63  % (20440)------------------------------
% 17.62/2.65  % (20441)Time limit reached!
% 17.62/2.65  % (20441)------------------------------
% 17.62/2.65  % (20441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.62/2.65  % (20441)Termination reason: Time limit
% 17.62/2.65  
% 17.62/2.65  % (20441)Memory used [KB]: 8571
% 17.62/2.65  % (20441)Time elapsed: 0.401 s
% 17.62/2.65  % (20441)------------------------------
% 17.62/2.65  % (20441)------------------------------
% 18.66/2.77  % (20444)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 19.47/2.83  % (20408)Time limit reached!
% 19.47/2.83  % (20408)------------------------------
% 19.47/2.83  % (20408)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.47/2.83  % (20408)Termination reason: Time limit
% 19.47/2.83  
% 19.47/2.83  % (20408)Memory used [KB]: 14967
% 19.47/2.83  % (20408)Time elapsed: 2.414 s
% 19.47/2.83  % (20408)------------------------------
% 19.47/2.83  % (20408)------------------------------
% 19.47/2.86  % (20406)Refutation found. Thanks to Tanya!
% 19.47/2.86  % SZS status Theorem for theBenchmark
% 19.47/2.86  % SZS output start Proof for theBenchmark
% 19.47/2.86  fof(f41473,plain,(
% 19.47/2.86    $false),
% 19.47/2.86    inference(avatar_sat_refutation,[],[f131,f140,f144,f148,f213,f292,f294,f296,f298,f306,f333,f336,f621,f623,f647,f654,f716,f735,f870,f878,f903,f1063,f1183,f1377,f1383,f1419,f1467,f3528,f3550,f6176,f6180,f40365,f40867,f41150,f41378])).
% 19.47/2.86  fof(f41378,plain,(
% 19.47/2.86    ~spl4_17),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f41161])).
% 19.47/2.86  fof(f41161,plain,(
% 19.47/2.86    $false | ~spl4_17),
% 19.47/2.86    inference(subsumption_resolution,[],[f65,f588])).
% 19.47/2.86  fof(f588,plain,(
% 19.47/2.86    sK3 = k2_funct_1(sK2) | ~spl4_17),
% 19.47/2.86    inference(avatar_component_clause,[],[f586])).
% 19.47/2.86  fof(f586,plain,(
% 19.47/2.86    spl4_17 <=> sK3 = k2_funct_1(sK2)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 19.47/2.86  fof(f65,plain,(
% 19.47/2.86    sK3 != k2_funct_1(sK2)),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f26,plain,(
% 19.47/2.86    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 19.47/2.86    inference(flattening,[],[f25])).
% 19.47/2.86  fof(f25,plain,(
% 19.47/2.86    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 19.47/2.86    inference(ennf_transformation,[],[f24])).
% 19.47/2.86  fof(f24,negated_conjecture,(
% 19.47/2.86    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 19.47/2.86    inference(negated_conjecture,[],[f23])).
% 19.47/2.86  fof(f23,conjecture,(
% 19.47/2.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 19.47/2.86  fof(f41150,plain,(
% 19.47/2.86    ~spl4_1 | ~spl4_90 | ~spl4_249 | ~spl4_485 | ~spl4_486 | ~spl4_3107),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f41147])).
% 19.47/2.86  fof(f41147,plain,(
% 19.47/2.86    $false | (~spl4_1 | ~spl4_90 | ~spl4_249 | ~spl4_485 | ~spl4_486 | ~spl4_3107)),
% 19.47/2.86    inference(unit_resulting_resolution,[],[f1376,f57,f126,f3523,f6036,f6040,f153,f41142,f217])).
% 19.47/2.86  fof(f217,plain,(
% 19.47/2.86    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_funct_1(X0)),X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0)) )),
% 19.47/2.86    inference(duplicate_literal_removal,[],[f216])).
% 19.47/2.86  fof(f216,plain,(
% 19.47/2.86    ( ! [X0,X1] : (~v4_relat_1(X0,X1) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(k2_funct_1(X0)),X1) | ~v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(superposition,[],[f176,f80])).
% 19.47/2.86  fof(f80,plain,(
% 19.47/2.86    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f32])).
% 19.47/2.86  fof(f32,plain,(
% 19.47/2.86    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.47/2.86    inference(flattening,[],[f31])).
% 19.47/2.86  fof(f31,plain,(
% 19.47/2.86    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.47/2.86    inference(ennf_transformation,[],[f12])).
% 19.47/2.86  fof(f12,axiom,(
% 19.47/2.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 19.47/2.86  fof(f176,plain,(
% 19.47/2.86    ( ! [X2,X1] : (~v4_relat_1(k2_funct_1(X1),X2) | ~v1_relat_1(k2_funct_1(X1)) | r1_tarski(k2_relat_1(X1),X2) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.47/2.86    inference(superposition,[],[f89,f81])).
% 19.47/2.86  fof(f81,plain,(
% 19.47/2.86    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f34])).
% 19.47/2.86  fof(f34,plain,(
% 19.47/2.86    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.47/2.86    inference(flattening,[],[f33])).
% 19.47/2.86  fof(f33,plain,(
% 19.47/2.86    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.47/2.86    inference(ennf_transformation,[],[f10])).
% 19.47/2.86  fof(f10,axiom,(
% 19.47/2.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 19.47/2.86  fof(f89,plain,(
% 19.47/2.86    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f41])).
% 19.47/2.86  fof(f41,plain,(
% 19.47/2.86    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.47/2.86    inference(ennf_transformation,[],[f2])).
% 19.47/2.86  fof(f2,axiom,(
% 19.47/2.86    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 19.47/2.86  fof(f41142,plain,(
% 19.47/2.86    ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),sK1) | ~spl4_3107),
% 19.47/2.86    inference(equality_resolution,[],[f40209])).
% 19.47/2.86  fof(f40209,plain,(
% 19.47/2.86    ( ! [X1] : (k6_partfun1(X1) != k6_partfun1(sK1) | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),X1)) ) | ~spl4_3107),
% 19.47/2.86    inference(avatar_component_clause,[],[f40208])).
% 19.47/2.86  fof(f40208,plain,(
% 19.47/2.86    spl4_3107 <=> ! [X1] : (k6_partfun1(X1) != k6_partfun1(sK1) | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),X1))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_3107])])).
% 19.47/2.86  fof(f153,plain,(
% 19.47/2.86    v4_relat_1(sK3,sK1)),
% 19.47/2.86    inference(resolution,[],[f91,f59])).
% 19.47/2.86  fof(f59,plain,(
% 19.47/2.86    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f91,plain,(
% 19.47/2.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f44])).
% 19.47/2.86  fof(f44,plain,(
% 19.47/2.86    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.47/2.86    inference(ennf_transformation,[],[f14])).
% 19.47/2.86  fof(f14,axiom,(
% 19.47/2.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 19.47/2.86  fof(f6040,plain,(
% 19.47/2.86    v1_funct_1(k2_funct_1(sK3)) | ~spl4_486),
% 19.47/2.86    inference(avatar_component_clause,[],[f6039])).
% 19.47/2.86  fof(f6039,plain,(
% 19.47/2.86    spl4_486 <=> v1_funct_1(k2_funct_1(sK3))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_486])])).
% 19.47/2.86  fof(f6036,plain,(
% 19.47/2.86    v2_funct_1(k2_funct_1(sK3)) | ~spl4_485),
% 19.47/2.86    inference(avatar_component_clause,[],[f6035])).
% 19.47/2.86  fof(f6035,plain,(
% 19.47/2.86    spl4_485 <=> v2_funct_1(k2_funct_1(sK3))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_485])])).
% 19.47/2.86  fof(f3523,plain,(
% 19.47/2.86    v1_relat_1(k2_funct_1(sK3)) | ~spl4_249),
% 19.47/2.86    inference(avatar_component_clause,[],[f3522])).
% 19.47/2.86  fof(f3522,plain,(
% 19.47/2.86    spl4_249 <=> v1_relat_1(k2_funct_1(sK3))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_249])])).
% 19.47/2.86  fof(f126,plain,(
% 19.47/2.86    v1_relat_1(sK3) | ~spl4_1),
% 19.47/2.86    inference(avatar_component_clause,[],[f124])).
% 19.47/2.86  fof(f124,plain,(
% 19.47/2.86    spl4_1 <=> v1_relat_1(sK3)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 19.47/2.86  fof(f57,plain,(
% 19.47/2.86    v1_funct_1(sK3)),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f1376,plain,(
% 19.47/2.86    v2_funct_1(sK3) | ~spl4_90),
% 19.47/2.86    inference(avatar_component_clause,[],[f1374])).
% 19.47/2.86  fof(f1374,plain,(
% 19.47/2.86    spl4_90 <=> v2_funct_1(sK3)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 19.47/2.86  fof(f40867,plain,(
% 19.47/2.86    ~spl4_1 | ~spl4_90 | ~spl4_20 | spl4_17 | ~spl4_3106),
% 19.47/2.86    inference(avatar_split_clause,[],[f40377,f40204,f586,f607,f1374,f124])).
% 19.47/2.86  fof(f607,plain,(
% 19.47/2.86    spl4_20 <=> v1_funct_1(sK3)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 19.47/2.86  fof(f40204,plain,(
% 19.47/2.86    spl4_3106 <=> sK2 = k2_funct_1(sK3)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_3106])])).
% 19.47/2.86  fof(f40377,plain,(
% 19.47/2.86    sK3 = k2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_3106),
% 19.47/2.86    inference(superposition,[],[f80,f40206])).
% 19.47/2.86  fof(f40206,plain,(
% 19.47/2.86    sK2 = k2_funct_1(sK3) | ~spl4_3106),
% 19.47/2.86    inference(avatar_component_clause,[],[f40204])).
% 19.47/2.86  fof(f40365,plain,(
% 19.47/2.86    ~spl4_3 | spl4_3106 | spl4_3107 | ~spl4_34 | ~spl4_52 | ~spl4_250),
% 19.47/2.86    inference(avatar_split_clause,[],[f40364,f3526,f900,f730,f40208,f40204,f133])).
% 19.47/2.86  fof(f133,plain,(
% 19.47/2.86    spl4_3 <=> v1_relat_1(sK2)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 19.47/2.86  fof(f730,plain,(
% 19.47/2.86    spl4_34 <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 19.47/2.86  fof(f900,plain,(
% 19.47/2.86    spl4_52 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 19.47/2.86  fof(f3526,plain,(
% 19.47/2.86    spl4_250 <=> ! [X49,X50] : (k6_partfun1(sK0) != k6_partfun1(k1_relat_1(X49)) | k2_funct_1(sK3) = X49 | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),X50) | k6_partfun1(X50) != k5_relat_1(k2_funct_1(sK2),X49) | ~v1_relat_1(X49))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_250])])).
% 19.47/2.86  fof(f40364,plain,(
% 19.47/2.86    ( ! [X22] : (k6_partfun1(sK1) != k6_partfun1(X22) | sK2 = k2_funct_1(sK3) | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),X22) | ~v1_relat_1(sK2)) ) | (~spl4_34 | ~spl4_52 | ~spl4_250)),
% 19.47/2.86    inference(trivial_inequality_removal,[],[f40363])).
% 19.47/2.86  fof(f40363,plain,(
% 19.47/2.86    ( ! [X22] : (k6_partfun1(sK0) != k6_partfun1(sK0) | k6_partfun1(sK1) != k6_partfun1(X22) | sK2 = k2_funct_1(sK3) | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),X22) | ~v1_relat_1(sK2)) ) | (~spl4_34 | ~spl4_52 | ~spl4_250)),
% 19.47/2.86    inference(forward_demodulation,[],[f40195,f732])).
% 19.47/2.86  fof(f732,plain,(
% 19.47/2.86    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~spl4_34),
% 19.47/2.86    inference(avatar_component_clause,[],[f730])).
% 19.47/2.86  fof(f40195,plain,(
% 19.47/2.86    ( ! [X22] : (k6_partfun1(sK1) != k6_partfun1(X22) | sK2 = k2_funct_1(sK3) | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),X22) | k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | (~spl4_52 | ~spl4_250)),
% 19.47/2.86    inference(superposition,[],[f3527,f902])).
% 19.47/2.86  fof(f902,plain,(
% 19.47/2.86    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~spl4_52),
% 19.47/2.86    inference(avatar_component_clause,[],[f900])).
% 19.47/2.86  fof(f3527,plain,(
% 19.47/2.86    ( ! [X50,X49] : (k6_partfun1(X50) != k5_relat_1(k2_funct_1(sK2),X49) | k2_funct_1(sK3) = X49 | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),X50) | k6_partfun1(sK0) != k6_partfun1(k1_relat_1(X49)) | ~v1_relat_1(X49)) ) | ~spl4_250),
% 19.47/2.86    inference(avatar_component_clause,[],[f3526])).
% 19.47/2.86  fof(f6180,plain,(
% 19.47/2.86    ~spl4_1 | spl4_486),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f6178])).
% 19.47/2.86  fof(f6178,plain,(
% 19.47/2.86    $false | (~spl4_1 | spl4_486)),
% 19.47/2.86    inference(unit_resulting_resolution,[],[f126,f57,f6041,f79])).
% 19.47/2.86  fof(f79,plain,(
% 19.47/2.86    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f30])).
% 19.47/2.86  fof(f30,plain,(
% 19.47/2.86    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.47/2.86    inference(flattening,[],[f29])).
% 19.47/2.86  fof(f29,plain,(
% 19.47/2.86    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.47/2.86    inference(ennf_transformation,[],[f7])).
% 19.47/2.86  fof(f7,axiom,(
% 19.47/2.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 19.47/2.86  fof(f6041,plain,(
% 19.47/2.86    ~v1_funct_1(k2_funct_1(sK3)) | spl4_486),
% 19.47/2.86    inference(avatar_component_clause,[],[f6039])).
% 19.47/2.86  fof(f6176,plain,(
% 19.47/2.86    ~spl4_1 | ~spl4_90 | spl4_485),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f6173])).
% 19.47/2.86  fof(f6173,plain,(
% 19.47/2.86    $false | (~spl4_1 | ~spl4_90 | spl4_485)),
% 19.47/2.86    inference(unit_resulting_resolution,[],[f1376,f57,f126,f6037,f341])).
% 19.47/2.86  fof(f341,plain,(
% 19.47/2.86    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0)) )),
% 19.47/2.86    inference(duplicate_literal_removal,[],[f337])).
% 19.47/2.86  fof(f337,plain,(
% 19.47/2.86    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(resolution,[],[f324,f78])).
% 19.47/2.86  fof(f78,plain,(
% 19.47/2.86    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f30])).
% 19.47/2.86  fof(f324,plain,(
% 19.47/2.86    ( ! [X0] : (~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) )),
% 19.47/2.86    inference(duplicate_literal_removal,[],[f320])).
% 19.47/2.86  fof(f320,plain,(
% 19.47/2.86    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(resolution,[],[f318,f79])).
% 19.47/2.86  fof(f318,plain,(
% 19.47/2.86    ( ! [X0] : (~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) )),
% 19.47/2.86    inference(trivial_inequality_removal,[],[f317])).
% 19.47/2.86  fof(f317,plain,(
% 19.47/2.86    ( ! [X0] : (k6_partfun1(k2_relat_1(X0)) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) )),
% 19.47/2.86    inference(duplicate_literal_removal,[],[f316])).
% 19.47/2.86  fof(f316,plain,(
% 19.47/2.86    ( ! [X0] : (k6_partfun1(k2_relat_1(X0)) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(superposition,[],[f191,f81])).
% 19.47/2.86  fof(f191,plain,(
% 19.47/2.86    ( ! [X2] : (k6_partfun1(k2_relat_1(X2)) != k6_partfun1(k1_relat_1(k2_funct_1(X2))) | ~v1_funct_1(k2_funct_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(k2_funct_1(X2)) | v2_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2)) )),
% 19.47/2.86    inference(duplicate_literal_removal,[],[f188])).
% 19.47/2.86  fof(f188,plain,(
% 19.47/2.86    ( ! [X2] : (k6_partfun1(k2_relat_1(X2)) != k6_partfun1(k1_relat_1(k2_funct_1(X2))) | ~v1_funct_1(k2_funct_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(k2_funct_1(X2)) | v2_funct_1(k2_funct_1(X2)) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.47/2.86    inference(superposition,[],[f114,f112])).
% 19.47/2.86  fof(f112,plain,(
% 19.47/2.86    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(definition_unfolding,[],[f84,f69])).
% 19.47/2.86  fof(f69,plain,(
% 19.47/2.86    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f19])).
% 19.47/2.86  fof(f19,axiom,(
% 19.47/2.86    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 19.47/2.86  fof(f84,plain,(
% 19.47/2.86    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f36])).
% 19.47/2.86  fof(f36,plain,(
% 19.47/2.86    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.47/2.86    inference(flattening,[],[f35])).
% 19.47/2.86  fof(f35,plain,(
% 19.47/2.86    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.47/2.86    inference(ennf_transformation,[],[f11])).
% 19.47/2.86  fof(f11,axiom,(
% 19.47/2.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 19.47/2.86  fof(f114,plain,(
% 19.47/2.86    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 19.47/2.86    inference(definition_unfolding,[],[f85,f69])).
% 19.47/2.86  fof(f85,plain,(
% 19.47/2.86    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f38])).
% 19.47/2.86  fof(f38,plain,(
% 19.47/2.86    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.47/2.86    inference(flattening,[],[f37])).
% 19.47/2.86  fof(f37,plain,(
% 19.47/2.86    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.47/2.86    inference(ennf_transformation,[],[f9])).
% 19.47/2.86  fof(f9,axiom,(
% 19.47/2.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).
% 19.47/2.86  fof(f6037,plain,(
% 19.47/2.86    ~v2_funct_1(k2_funct_1(sK3)) | spl4_485),
% 19.47/2.86    inference(avatar_component_clause,[],[f6035])).
% 19.47/2.86  fof(f3550,plain,(
% 19.47/2.86    ~spl4_1 | spl4_249),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f3548])).
% 19.47/2.86  fof(f3548,plain,(
% 19.47/2.86    $false | (~spl4_1 | spl4_249)),
% 19.47/2.86    inference(unit_resulting_resolution,[],[f126,f57,f3524,f78])).
% 19.47/2.86  fof(f3524,plain,(
% 19.47/2.86    ~v1_relat_1(k2_funct_1(sK3)) | spl4_249),
% 19.47/2.86    inference(avatar_component_clause,[],[f3522])).
% 19.47/2.86  fof(f3528,plain,(
% 19.47/2.86    ~spl4_3 | ~spl4_90 | ~spl4_9 | ~spl4_20 | ~spl4_1 | ~spl4_8 | ~spl4_249 | ~spl4_13 | spl4_250 | ~spl4_23 | ~spl4_33 | ~spl4_92),
% 19.47/2.86    inference(avatar_split_clause,[],[f3520,f1464,f725,f632,f3526,f330,f3522,f277,f124,f607,f281,f1374,f133])).
% 19.47/2.86  fof(f281,plain,(
% 19.47/2.86    spl4_9 <=> v2_funct_1(sK2)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 19.47/2.86  fof(f277,plain,(
% 19.47/2.86    spl4_8 <=> v1_funct_1(sK2)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 19.47/2.86  fof(f330,plain,(
% 19.47/2.86    spl4_13 <=> v1_relat_1(k2_funct_1(sK2))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 19.47/2.86  fof(f632,plain,(
% 19.47/2.86    spl4_23 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 19.47/2.86  fof(f725,plain,(
% 19.47/2.86    spl4_33 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(k2_funct_1(sK2)))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 19.47/2.86  fof(f1464,plain,(
% 19.47/2.86    spl4_92 <=> k6_partfun1(k2_relat_1(k2_funct_1(sK2))) = k2_funct_1(k6_partfun1(sK0))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).
% 19.47/2.86  fof(f3520,plain,(
% 19.47/2.86    ( ! [X50,X49] : (k6_partfun1(sK0) != k6_partfun1(k1_relat_1(X49)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X49) | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),X50) | ~v1_relat_1(k2_funct_1(sK3)) | k6_partfun1(X50) != k5_relat_1(k2_funct_1(sK2),X49) | k2_funct_1(sK3) = X49 | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2)) ) | (~spl4_23 | ~spl4_33 | ~spl4_92)),
% 19.47/2.86    inference(forward_demodulation,[],[f3413,f2018])).
% 19.47/2.86  fof(f2018,plain,(
% 19.47/2.86    k6_partfun1(sK0) = k2_funct_1(k6_partfun1(sK0)) | (~spl4_33 | ~spl4_92)),
% 19.47/2.86    inference(forward_demodulation,[],[f1466,f727])).
% 19.47/2.86  fof(f727,plain,(
% 19.47/2.86    k6_partfun1(sK0) = k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | ~spl4_33),
% 19.47/2.86    inference(avatar_component_clause,[],[f725])).
% 19.47/2.86  fof(f1466,plain,(
% 19.47/2.86    k6_partfun1(k2_relat_1(k2_funct_1(sK2))) = k2_funct_1(k6_partfun1(sK0)) | ~spl4_92),
% 19.47/2.86    inference(avatar_component_clause,[],[f1464])).
% 19.47/2.86  fof(f3413,plain,(
% 19.47/2.86    ( ! [X50,X49] : (k2_funct_1(k6_partfun1(sK0)) != k6_partfun1(k1_relat_1(X49)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X49) | ~r1_tarski(k2_relat_1(k2_funct_1(sK3)),X50) | ~v1_relat_1(k2_funct_1(sK3)) | k6_partfun1(X50) != k5_relat_1(k2_funct_1(sK2),X49) | k2_funct_1(sK3) = X49 | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2)) ) | ~spl4_23),
% 19.47/2.86    inference(superposition,[],[f460,f634])).
% 19.47/2.86  fof(f634,plain,(
% 19.47/2.86    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_23),
% 19.47/2.86    inference(avatar_component_clause,[],[f632])).
% 19.47/2.86  fof(f460,plain,(
% 19.47/2.86    ( ! [X24,X23,X21,X22] : (k2_funct_1(k5_relat_1(X22,X21)) != k6_partfun1(k1_relat_1(X23)) | ~v1_relat_1(k2_funct_1(X22)) | ~v1_relat_1(X23) | ~r1_tarski(k2_relat_1(k2_funct_1(X21)),X24) | ~v1_relat_1(k2_funct_1(X21)) | k6_partfun1(X24) != k5_relat_1(k2_funct_1(X22),X23) | k2_funct_1(X21) = X23 | ~v1_funct_1(X22) | ~v1_relat_1(X21) | ~v1_funct_1(X21) | ~v2_funct_1(X22) | ~v2_funct_1(X21) | ~v1_relat_1(X22)) )),
% 19.47/2.86    inference(superposition,[],[f115,f86])).
% 19.47/2.86  fof(f86,plain,(
% 19.47/2.86    ( ! [X0,X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v2_funct_1(X1) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f40])).
% 19.47/2.86  fof(f40,plain,(
% 19.47/2.86    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 19.47/2.86    inference(flattening,[],[f39])).
% 19.47/2.86  fof(f39,plain,(
% 19.47/2.86    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 19.47/2.86    inference(ennf_transformation,[],[f13])).
% 19.47/2.86  fof(f13,axiom,(
% 19.47/2.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).
% 19.47/2.86  fof(f115,plain,(
% 19.47/2.86    ( ! [X2,X0,X3,X1] : (k5_relat_1(X1,X2) != k6_partfun1(k1_relat_1(X3)) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k5_relat_1(X2,X3) != k6_partfun1(X0) | X1 = X3) )),
% 19.47/2.86    inference(definition_unfolding,[],[f90,f69,f69])).
% 19.47/2.86  fof(f90,plain,(
% 19.47/2.86    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | k6_relat_1(X0) != k5_relat_1(X2,X3) | X1 = X3) )),
% 19.47/2.86    inference(cnf_transformation,[],[f43])).
% 19.47/2.86  fof(f43,plain,(
% 19.47/2.86    ! [X0,X1] : (! [X2] : (! [X3] : (X1 = X3 | k6_relat_1(X0) != k5_relat_1(X2,X3) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 19.47/2.86    inference(flattening,[],[f42])).
% 19.47/2.86  fof(f42,plain,(
% 19.47/2.86    ! [X0,X1] : (! [X2] : (! [X3] : ((X1 = X3 | (k6_relat_1(X0) != k5_relat_1(X2,X3) | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3)) | ~r1_tarski(k2_relat_1(X1),X0))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 19.47/2.86    inference(ennf_transformation,[],[f6])).
% 19.47/2.86  fof(f6,axiom,(
% 19.47/2.86    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_relat_1)).
% 19.47/2.86  fof(f1467,plain,(
% 19.47/2.86    ~spl4_3 | ~spl4_9 | ~spl4_8 | ~spl4_13 | ~spl4_12 | ~spl4_7 | spl4_92 | ~spl4_31),
% 19.47/2.86    inference(avatar_split_clause,[],[f1428,f709,f1464,f273,f326,f330,f277,f281,f133])).
% 19.47/2.86  fof(f326,plain,(
% 19.47/2.86    spl4_12 <=> v2_funct_1(k2_funct_1(sK2))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 19.47/2.86  fof(f273,plain,(
% 19.47/2.86    spl4_7 <=> v1_funct_1(k2_funct_1(sK2))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 19.47/2.86  fof(f709,plain,(
% 19.47/2.86    spl4_31 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 19.47/2.86  fof(f1428,plain,(
% 19.47/2.86    k6_partfun1(k2_relat_1(k2_funct_1(sK2))) = k2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_31),
% 19.47/2.86    inference(superposition,[],[f238,f711])).
% 19.47/2.86  fof(f711,plain,(
% 19.47/2.86    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_31),
% 19.47/2.86    inference(avatar_component_clause,[],[f709])).
% 19.47/2.86  fof(f238,plain,(
% 19.47/2.86    ( ! [X1] : (k2_funct_1(k5_relat_1(X1,k2_funct_1(X1))) = k6_partfun1(k2_relat_1(k2_funct_1(X1))) | ~v1_funct_1(k2_funct_1(X1)) | ~v2_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.47/2.86    inference(duplicate_literal_removal,[],[f236])).
% 19.47/2.86  fof(f236,plain,(
% 19.47/2.86    ( ! [X1] : (k2_funct_1(k5_relat_1(X1,k2_funct_1(X1))) = k6_partfun1(k2_relat_1(k2_funct_1(X1))) | ~v1_funct_1(k2_funct_1(X1)) | ~v2_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v2_funct_1(k2_funct_1(X1)) | ~v1_relat_1(X1)) )),
% 19.47/2.86    inference(superposition,[],[f112,f86])).
% 19.47/2.86  fof(f1419,plain,(
% 19.47/2.86    ~spl4_89),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f1384])).
% 19.47/2.86  fof(f1384,plain,(
% 19.47/2.86    $false | ~spl4_89),
% 19.47/2.86    inference(subsumption_resolution,[],[f63,f1372])).
% 19.47/2.86  fof(f1372,plain,(
% 19.47/2.86    k1_xboole_0 = sK0 | ~spl4_89),
% 19.47/2.86    inference(avatar_component_clause,[],[f1370])).
% 19.47/2.86  fof(f1370,plain,(
% 19.47/2.86    spl4_89 <=> k1_xboole_0 = sK0),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).
% 19.47/2.86  fof(f63,plain,(
% 19.47/2.86    k1_xboole_0 != sK0),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f1383,plain,(
% 19.47/2.86    spl4_88),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f1382])).
% 19.47/2.86  fof(f1382,plain,(
% 19.47/2.86    $false | spl4_88),
% 19.47/2.86    inference(subsumption_resolution,[],[f58,f1368])).
% 19.47/2.86  fof(f1368,plain,(
% 19.47/2.86    ~v1_funct_2(sK3,sK1,sK0) | spl4_88),
% 19.47/2.86    inference(avatar_component_clause,[],[f1366])).
% 19.47/2.86  fof(f1366,plain,(
% 19.47/2.86    spl4_88 <=> v1_funct_2(sK3,sK1,sK0)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 19.47/2.86  fof(f58,plain,(
% 19.47/2.86    v1_funct_2(sK3,sK1,sK0)),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f1377,plain,(
% 19.47/2.86    ~spl4_88 | ~spl4_19 | ~spl4_20 | spl4_89 | spl4_90 | ~spl4_43 | ~spl4_6 | ~spl4_76),
% 19.47/2.86    inference(avatar_split_clause,[],[f1362,f1181,f210,f804,f1374,f1370,f607,f603,f1366])).
% 19.47/2.86  fof(f603,plain,(
% 19.47/2.86    spl4_19 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 19.47/2.86  fof(f804,plain,(
% 19.47/2.86    spl4_43 <=> v2_funct_1(k6_partfun1(sK0))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 19.47/2.86  fof(f210,plain,(
% 19.47/2.86    spl4_6 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 19.47/2.86  fof(f1181,plain,(
% 19.47/2.86    spl4_76 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 19.47/2.86  fof(f1362,plain,(
% 19.47/2.86    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_6 | ~spl4_76)),
% 19.47/2.86    inference(superposition,[],[f1182,f212])).
% 19.47/2.86  fof(f212,plain,(
% 19.47/2.86    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_6),
% 19.47/2.86    inference(avatar_component_clause,[],[f210])).
% 19.47/2.86  fof(f1182,plain,(
% 19.47/2.86    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_76),
% 19.47/2.86    inference(avatar_component_clause,[],[f1181])).
% 19.47/2.86  fof(f1183,plain,(
% 19.47/2.86    ~spl4_8 | spl4_76 | ~spl4_10 | ~spl4_11),
% 19.47/2.86    inference(avatar_split_clause,[],[f1179,f289,f285,f1181,f277])).
% 19.47/2.86  fof(f285,plain,(
% 19.47/2.86    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 19.47/2.86  fof(f289,plain,(
% 19.47/2.86    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 19.47/2.86  fof(f1179,plain,(
% 19.47/2.86    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 19.47/2.86    inference(trivial_inequality_removal,[],[f1178])).
% 19.47/2.86  fof(f1178,plain,(
% 19.47/2.86    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 19.47/2.86    inference(superposition,[],[f101,f60])).
% 19.47/2.86  fof(f60,plain,(
% 19.47/2.86    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f101,plain,(
% 19.47/2.86    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f50])).
% 19.47/2.86  fof(f50,plain,(
% 19.47/2.86    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 19.47/2.86    inference(flattening,[],[f49])).
% 19.47/2.86  fof(f49,plain,(
% 19.47/2.86    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 19.47/2.86    inference(ennf_transformation,[],[f20])).
% 19.47/2.86  fof(f20,axiom,(
% 19.47/2.86    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 19.47/2.86  fof(f1063,plain,(
% 19.47/2.86    ~spl4_3 | ~spl4_9 | ~spl4_8 | ~spl4_13 | ~spl4_12 | ~spl4_7 | spl4_33 | ~spl4_31),
% 19.47/2.86    inference(avatar_split_clause,[],[f1058,f709,f725,f273,f326,f330,f277,f281,f133])).
% 19.47/2.86  fof(f1058,plain,(
% 19.47/2.86    k6_partfun1(sK0) = k6_partfun1(k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_31),
% 19.47/2.86    inference(superposition,[],[f180,f711])).
% 19.47/2.86  fof(f180,plain,(
% 19.47/2.86    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k2_relat_1(k2_funct_1(X0))) | ~v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(superposition,[],[f112,f80])).
% 19.47/2.86  fof(f903,plain,(
% 19.47/2.86    spl4_52 | spl4_32 | ~spl4_9 | ~spl4_8 | ~spl4_10 | ~spl4_11),
% 19.47/2.86    inference(avatar_split_clause,[],[f898,f289,f285,f277,f281,f713,f900])).
% 19.47/2.86  fof(f713,plain,(
% 19.47/2.86    spl4_32 <=> k1_xboole_0 = sK1),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 19.47/2.86  fof(f898,plain,(
% 19.47/2.86    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 19.47/2.86    inference(trivial_inequality_removal,[],[f897])).
% 19.47/2.86  fof(f897,plain,(
% 19.47/2.86    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 19.47/2.86    inference(superposition,[],[f97,f60])).
% 19.47/2.86  fof(f97,plain,(
% 19.47/2.86    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f48])).
% 19.47/2.86  fof(f48,plain,(
% 19.47/2.86    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 19.47/2.86    inference(flattening,[],[f47])).
% 19.47/2.86  fof(f47,plain,(
% 19.47/2.86    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 19.47/2.86    inference(ennf_transformation,[],[f22])).
% 19.47/2.86  fof(f22,axiom,(
% 19.47/2.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 19.47/2.86  fof(f878,plain,(
% 19.47/2.86    spl4_43),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f873])).
% 19.47/2.86  fof(f873,plain,(
% 19.47/2.86    $false | spl4_43),
% 19.47/2.86    inference(unit_resulting_resolution,[],[f107,f108,f806,f195])).
% 19.47/2.86  fof(f195,plain,(
% 19.47/2.86    ( ! [X1] : (~v1_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1)) | v2_funct_1(k6_partfun1(X1))) )),
% 19.47/2.86    inference(trivial_inequality_removal,[],[f194])).
% 19.47/2.86  fof(f194,plain,(
% 19.47/2.86    ( ! [X1] : (k6_partfun1(X1) != k6_partfun1(X1) | ~v1_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1)) | v2_funct_1(k6_partfun1(X1))) )),
% 19.47/2.86    inference(forward_demodulation,[],[f192,f110])).
% 19.47/2.86  fof(f110,plain,(
% 19.47/2.86    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 19.47/2.86    inference(definition_unfolding,[],[f74,f69])).
% 19.47/2.86  fof(f74,plain,(
% 19.47/2.86    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 19.47/2.86    inference(cnf_transformation,[],[f4])).
% 19.47/2.86  fof(f4,axiom,(
% 19.47/2.86    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 19.47/2.86  fof(f192,plain,(
% 19.47/2.86    ( ! [X1] : (k6_partfun1(X1) != k6_partfun1(k1_relat_1(k6_partfun1(X1))) | ~v1_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1)) | v2_funct_1(k6_partfun1(X1))) )),
% 19.47/2.86    inference(duplicate_literal_removal,[],[f187])).
% 19.47/2.86  fof(f187,plain,(
% 19.47/2.86    ( ! [X1] : (k6_partfun1(X1) != k6_partfun1(k1_relat_1(k6_partfun1(X1))) | ~v1_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1)) | ~v1_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1)) | v2_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1))) )),
% 19.47/2.86    inference(superposition,[],[f114,f159])).
% 19.47/2.86  fof(f159,plain,(
% 19.47/2.86    ( ! [X0] : (k6_partfun1(X0) = k5_relat_1(k6_partfun1(X0),k6_partfun1(X0)) | ~v1_relat_1(k6_partfun1(X0))) )),
% 19.47/2.86    inference(superposition,[],[f111,f109])).
% 19.47/2.86  fof(f109,plain,(
% 19.47/2.86    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 19.47/2.86    inference(definition_unfolding,[],[f75,f69])).
% 19.47/2.86  fof(f75,plain,(
% 19.47/2.86    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 19.47/2.86    inference(cnf_transformation,[],[f4])).
% 19.47/2.86  fof(f111,plain,(
% 19.47/2.86    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(definition_unfolding,[],[f76,f69])).
% 19.47/2.86  fof(f76,plain,(
% 19.47/2.86    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 19.47/2.86    inference(cnf_transformation,[],[f27])).
% 19.47/2.86  fof(f27,plain,(
% 19.47/2.86    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 19.47/2.86    inference(ennf_transformation,[],[f5])).
% 19.47/2.86  fof(f5,axiom,(
% 19.47/2.86    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 19.47/2.86  fof(f806,plain,(
% 19.47/2.86    ~v2_funct_1(k6_partfun1(sK0)) | spl4_43),
% 19.47/2.86    inference(avatar_component_clause,[],[f804])).
% 19.47/2.86  fof(f108,plain,(
% 19.47/2.86    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 19.47/2.86    inference(definition_unfolding,[],[f70,f69])).
% 19.47/2.86  fof(f70,plain,(
% 19.47/2.86    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 19.47/2.86    inference(cnf_transformation,[],[f8])).
% 19.47/2.86  fof(f8,axiom,(
% 19.47/2.86    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 19.47/2.86  fof(f107,plain,(
% 19.47/2.86    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 19.47/2.86    inference(definition_unfolding,[],[f71,f69])).
% 19.47/2.86  fof(f71,plain,(
% 19.47/2.86    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 19.47/2.86    inference(cnf_transformation,[],[f8])).
% 19.47/2.86  fof(f870,plain,(
% 19.47/2.86    ~spl4_32),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f849])).
% 19.47/2.86  fof(f849,plain,(
% 19.47/2.86    $false | ~spl4_32),
% 19.47/2.86    inference(subsumption_resolution,[],[f64,f715])).
% 19.47/2.86  fof(f715,plain,(
% 19.47/2.86    k1_xboole_0 = sK1 | ~spl4_32),
% 19.47/2.86    inference(avatar_component_clause,[],[f713])).
% 19.47/2.86  fof(f64,plain,(
% 19.47/2.86    k1_xboole_0 != sK1),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f735,plain,(
% 19.47/2.86    ~spl4_3 | ~spl4_9 | ~spl4_8 | spl4_34 | ~spl4_31),
% 19.47/2.86    inference(avatar_split_clause,[],[f721,f709,f730,f277,f281,f133])).
% 19.47/2.86  fof(f721,plain,(
% 19.47/2.86    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_31),
% 19.47/2.86    inference(superposition,[],[f113,f711])).
% 19.47/2.86  fof(f113,plain,(
% 19.47/2.86    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 19.47/2.86    inference(definition_unfolding,[],[f83,f69])).
% 19.47/2.86  fof(f83,plain,(
% 19.47/2.86    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 19.47/2.86    inference(cnf_transformation,[],[f36])).
% 19.47/2.86  fof(f716,plain,(
% 19.47/2.86    spl4_31 | spl4_32 | ~spl4_9 | ~spl4_8 | ~spl4_10 | ~spl4_11),
% 19.47/2.86    inference(avatar_split_clause,[],[f707,f289,f285,f277,f281,f713,f709])).
% 19.47/2.86  fof(f707,plain,(
% 19.47/2.86    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 19.47/2.86    inference(trivial_inequality_removal,[],[f706])).
% 19.47/2.86  fof(f706,plain,(
% 19.47/2.86    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 19.47/2.86    inference(superposition,[],[f96,f60])).
% 19.47/2.86  fof(f96,plain,(
% 19.47/2.86    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 19.47/2.86    inference(cnf_transformation,[],[f48])).
% 19.47/2.86  fof(f654,plain,(
% 19.47/2.86    ~spl4_8 | ~spl4_19 | ~spl4_20 | ~spl4_10 | spl4_23 | ~spl4_6),
% 19.47/2.86    inference(avatar_split_clause,[],[f651,f210,f632,f285,f607,f603,f277])).
% 19.47/2.86  fof(f651,plain,(
% 19.47/2.86    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_6),
% 19.47/2.86    inference(superposition,[],[f104,f212])).
% 19.47/2.86  fof(f104,plain,(
% 19.47/2.86    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f54])).
% 19.47/2.86  fof(f54,plain,(
% 19.47/2.86    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 19.47/2.86    inference(flattening,[],[f53])).
% 19.47/2.86  fof(f53,plain,(
% 19.47/2.86    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 19.47/2.86    inference(ennf_transformation,[],[f18])).
% 19.47/2.86  fof(f18,axiom,(
% 19.47/2.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 19.47/2.86  fof(f647,plain,(
% 19.47/2.86    spl4_5),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f636])).
% 19.47/2.86  fof(f636,plain,(
% 19.47/2.86    $false | spl4_5),
% 19.47/2.86    inference(unit_resulting_resolution,[],[f66,f57,f59,f68,f208,f106])).
% 19.47/2.86  fof(f106,plain,(
% 19.47/2.86    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f56])).
% 19.47/2.86  fof(f56,plain,(
% 19.47/2.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 19.47/2.86    inference(flattening,[],[f55])).
% 19.47/2.86  fof(f55,plain,(
% 19.47/2.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 19.47/2.86    inference(ennf_transformation,[],[f16])).
% 19.47/2.86  fof(f16,axiom,(
% 19.47/2.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 19.47/2.86  fof(f208,plain,(
% 19.47/2.86    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_5),
% 19.47/2.86    inference(avatar_component_clause,[],[f206])).
% 19.47/2.86  fof(f206,plain,(
% 19.47/2.86    spl4_5 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 19.47/2.86  fof(f68,plain,(
% 19.47/2.86    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f66,plain,(
% 19.47/2.86    v1_funct_1(sK2)),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f623,plain,(
% 19.47/2.86    spl4_20),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f622])).
% 19.47/2.86  fof(f622,plain,(
% 19.47/2.86    $false | spl4_20),
% 19.47/2.86    inference(subsumption_resolution,[],[f57,f609])).
% 19.47/2.86  fof(f609,plain,(
% 19.47/2.86    ~v1_funct_1(sK3) | spl4_20),
% 19.47/2.86    inference(avatar_component_clause,[],[f607])).
% 19.47/2.86  fof(f621,plain,(
% 19.47/2.86    spl4_19),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f620])).
% 19.47/2.86  fof(f620,plain,(
% 19.47/2.86    $false | spl4_19),
% 19.47/2.86    inference(subsumption_resolution,[],[f59,f605])).
% 19.47/2.86  fof(f605,plain,(
% 19.47/2.86    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_19),
% 19.47/2.86    inference(avatar_component_clause,[],[f603])).
% 19.47/2.86  fof(f336,plain,(
% 19.47/2.86    ~spl4_3 | spl4_13),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f334])).
% 19.47/2.86  fof(f334,plain,(
% 19.47/2.86    $false | (~spl4_3 | spl4_13)),
% 19.47/2.86    inference(unit_resulting_resolution,[],[f135,f66,f332,f78])).
% 19.47/2.86  fof(f332,plain,(
% 19.47/2.86    ~v1_relat_1(k2_funct_1(sK2)) | spl4_13),
% 19.47/2.86    inference(avatar_component_clause,[],[f330])).
% 19.47/2.86  fof(f135,plain,(
% 19.47/2.86    v1_relat_1(sK2) | ~spl4_3),
% 19.47/2.86    inference(avatar_component_clause,[],[f133])).
% 19.47/2.86  fof(f333,plain,(
% 19.47/2.86    ~spl4_9 | spl4_12 | ~spl4_13 | ~spl4_8 | ~spl4_3 | ~spl4_7),
% 19.47/2.86    inference(avatar_split_clause,[],[f321,f273,f133,f277,f330,f326,f281])).
% 19.47/2.86  fof(f321,plain,(
% 19.47/2.86    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~spl4_7),
% 19.47/2.86    inference(resolution,[],[f318,f275])).
% 19.47/2.86  fof(f275,plain,(
% 19.47/2.86    v1_funct_1(k2_funct_1(sK2)) | ~spl4_7),
% 19.47/2.86    inference(avatar_component_clause,[],[f273])).
% 19.47/2.86  fof(f306,plain,(
% 19.47/2.86    spl4_11),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f305])).
% 19.47/2.86  fof(f305,plain,(
% 19.47/2.86    $false | spl4_11),
% 19.47/2.86    inference(subsumption_resolution,[],[f67,f291])).
% 19.47/2.86  fof(f291,plain,(
% 19.47/2.86    ~v1_funct_2(sK2,sK0,sK1) | spl4_11),
% 19.47/2.86    inference(avatar_component_clause,[],[f289])).
% 19.47/2.86  fof(f67,plain,(
% 19.47/2.86    v1_funct_2(sK2,sK0,sK1)),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f298,plain,(
% 19.47/2.86    spl4_10),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f297])).
% 19.47/2.86  fof(f297,plain,(
% 19.47/2.86    $false | spl4_10),
% 19.47/2.86    inference(subsumption_resolution,[],[f68,f287])).
% 19.47/2.86  fof(f287,plain,(
% 19.47/2.86    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_10),
% 19.47/2.86    inference(avatar_component_clause,[],[f285])).
% 19.47/2.86  fof(f296,plain,(
% 19.47/2.86    spl4_9),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f295])).
% 19.47/2.86  fof(f295,plain,(
% 19.47/2.86    $false | spl4_9),
% 19.47/2.86    inference(subsumption_resolution,[],[f62,f283])).
% 19.47/2.86  fof(f283,plain,(
% 19.47/2.86    ~v2_funct_1(sK2) | spl4_9),
% 19.47/2.86    inference(avatar_component_clause,[],[f281])).
% 19.47/2.86  fof(f62,plain,(
% 19.47/2.86    v2_funct_1(sK2)),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f294,plain,(
% 19.47/2.86    spl4_8),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f293])).
% 19.47/2.86  fof(f293,plain,(
% 19.47/2.86    $false | spl4_8),
% 19.47/2.86    inference(subsumption_resolution,[],[f66,f279])).
% 19.47/2.86  fof(f279,plain,(
% 19.47/2.86    ~v1_funct_1(sK2) | spl4_8),
% 19.47/2.86    inference(avatar_component_clause,[],[f277])).
% 19.47/2.86  fof(f292,plain,(
% 19.47/2.86    spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11),
% 19.47/2.86    inference(avatar_split_clause,[],[f271,f289,f285,f281,f277,f273])).
% 19.47/2.86  fof(f271,plain,(
% 19.47/2.86    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 19.47/2.86    inference(trivial_inequality_removal,[],[f270])).
% 19.47/2.86  fof(f270,plain,(
% 19.47/2.86    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 19.47/2.86    inference(superposition,[],[f93,f60])).
% 19.47/2.86  fof(f93,plain,(
% 19.47/2.86    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_1(k2_funct_1(X2))) )),
% 19.47/2.86    inference(cnf_transformation,[],[f46])).
% 19.47/2.86  fof(f46,plain,(
% 19.47/2.86    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 19.47/2.86    inference(flattening,[],[f45])).
% 19.47/2.86  fof(f45,plain,(
% 19.47/2.86    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 19.47/2.86    inference(ennf_transformation,[],[f21])).
% 19.47/2.86  fof(f21,axiom,(
% 19.47/2.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 19.47/2.86  fof(f213,plain,(
% 19.47/2.86    ~spl4_5 | spl4_6),
% 19.47/2.86    inference(avatar_split_clause,[],[f203,f210,f206])).
% 19.47/2.86  fof(f203,plain,(
% 19.47/2.86    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 19.47/2.86    inference(resolution,[],[f200,f61])).
% 19.47/2.86  fof(f61,plain,(
% 19.47/2.86    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 19.47/2.86    inference(cnf_transformation,[],[f26])).
% 19.47/2.86  fof(f200,plain,(
% 19.47/2.86    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 19.47/2.86    inference(resolution,[],[f103,f73])).
% 19.47/2.86  fof(f73,plain,(
% 19.47/2.86    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 19.47/2.86    inference(cnf_transformation,[],[f17])).
% 19.47/2.86  fof(f17,axiom,(
% 19.47/2.86    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 19.47/2.86  fof(f103,plain,(
% 19.47/2.86    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f52])).
% 19.47/2.86  fof(f52,plain,(
% 19.47/2.86    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.47/2.86    inference(flattening,[],[f51])).
% 19.47/2.86  fof(f51,plain,(
% 19.47/2.86    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 19.47/2.86    inference(ennf_transformation,[],[f15])).
% 19.47/2.86  fof(f15,axiom,(
% 19.47/2.86    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 19.47/2.86  fof(f148,plain,(
% 19.47/2.86    spl4_4),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f145])).
% 19.47/2.86  fof(f145,plain,(
% 19.47/2.86    $false | spl4_4),
% 19.47/2.86    inference(unit_resulting_resolution,[],[f87,f139])).
% 19.47/2.86  fof(f139,plain,(
% 19.47/2.86    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 19.47/2.86    inference(avatar_component_clause,[],[f137])).
% 19.47/2.86  fof(f137,plain,(
% 19.47/2.86    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 19.47/2.86  fof(f87,plain,(
% 19.47/2.86    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 19.47/2.86    inference(cnf_transformation,[],[f3])).
% 19.47/2.86  fof(f3,axiom,(
% 19.47/2.86    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 19.47/2.86  fof(f144,plain,(
% 19.47/2.86    spl4_2),
% 19.47/2.86    inference(avatar_contradiction_clause,[],[f141])).
% 19.47/2.86  fof(f141,plain,(
% 19.47/2.86    $false | spl4_2),
% 19.47/2.86    inference(unit_resulting_resolution,[],[f87,f130])).
% 19.47/2.86  fof(f130,plain,(
% 19.47/2.86    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 19.47/2.86    inference(avatar_component_clause,[],[f128])).
% 19.47/2.86  fof(f128,plain,(
% 19.47/2.86    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 19.47/2.86    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 19.47/2.86  fof(f140,plain,(
% 19.47/2.86    spl4_3 | ~spl4_4),
% 19.47/2.86    inference(avatar_split_clause,[],[f121,f137,f133])).
% 19.47/2.86  fof(f121,plain,(
% 19.47/2.86    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 19.47/2.86    inference(resolution,[],[f77,f68])).
% 19.47/2.86  fof(f77,plain,(
% 19.47/2.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 19.47/2.86    inference(cnf_transformation,[],[f28])).
% 19.47/2.86  fof(f28,plain,(
% 19.47/2.86    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 19.47/2.86    inference(ennf_transformation,[],[f1])).
% 19.47/2.86  fof(f1,axiom,(
% 19.47/2.86    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 19.47/2.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 19.47/2.86  fof(f131,plain,(
% 19.47/2.86    spl4_1 | ~spl4_2),
% 19.47/2.86    inference(avatar_split_clause,[],[f120,f128,f124])).
% 19.47/2.86  fof(f120,plain,(
% 19.47/2.86    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 19.47/2.86    inference(resolution,[],[f77,f59])).
% 19.47/2.86  % SZS output end Proof for theBenchmark
% 19.47/2.86  % (20406)------------------------------
% 19.47/2.86  % (20406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.47/2.86  % (20406)Termination reason: Refutation
% 19.47/2.86  
% 19.47/2.86  % (20406)Memory used [KB]: 33261
% 19.47/2.86  % (20406)Time elapsed: 2.446 s
% 19.47/2.86  % (20406)------------------------------
% 19.47/2.86  % (20406)------------------------------
% 19.47/2.88  % (20392)Success in time 2.516 s
%------------------------------------------------------------------------------
