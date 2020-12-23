%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 261 expanded)
%              Number of leaves         :   28 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  451 (1169 expanded)
%              Number of equality atoms :   78 ( 320 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f351,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f60,f65,f70,f80,f85,f95,f110,f111,f128,f157,f186,f188,f197,f249,f272,f281,f321,f349])).

fof(f349,plain,
    ( ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_29
    | spl5_32 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_29
    | spl5_32 ),
    inference(subsumption_resolution,[],[f347,f271])).

fof(f271,plain,
    ( ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_32 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl5_32
  <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f347,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f327,f248])).

fof(f248,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl5_29
  <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f327,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f94,f79,f84,f69,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f69,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f84,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f79,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_7
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f94,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_10
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f321,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_20
    | spl5_33 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_20
    | spl5_33 ),
    inference(subsumption_resolution,[],[f319,f156])).

fof(f156,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_18
  <=> r1_tarski(k1_relat_1(sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f319,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_20
    | spl5_33 ),
    inference(forward_demodulation,[],[f318,f173])).

fof(f173,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl5_19
  <=> sK1 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f318,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_20
    | spl5_33 ),
    inference(subsumption_resolution,[],[f317,f108])).

fof(f108,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl5_12
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f317,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))
    | ~ v1_relat_1(sK4)
    | ~ spl5_11
    | ~ spl5_20
    | spl5_33 ),
    inference(subsumption_resolution,[],[f316,f103])).

fof(f103,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f316,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ spl5_20
    | spl5_33 ),
    inference(subsumption_resolution,[],[f315,f179])).

fof(f179,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl5_20
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f315,plain,
    ( sK2 != k2_relat_1(sK4)
    | ~ r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | spl5_33 ),
    inference(superposition,[],[f280,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f280,plain,
    ( sK2 != k2_relat_1(k5_relat_1(sK3,sK4))
    | spl5_33 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl5_33
  <=> sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f281,plain,
    ( ~ spl5_33
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | spl5_22 ),
    inference(avatar_split_clause,[],[f276,f194,f92,f82,f77,f67,f278])).

fof(f194,plain,
    ( spl5_22
  <=> sK2 = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f276,plain,
    ( sK2 != k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | spl5_22 ),
    inference(subsumption_resolution,[],[f275,f94])).

fof(f275,plain,
    ( sK2 != k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK3)
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | spl5_22 ),
    inference(subsumption_resolution,[],[f274,f84])).

fof(f274,plain,
    ( sK2 != k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl5_5
    | ~ spl5_7
    | spl5_22 ),
    inference(subsumption_resolution,[],[f273,f79])).

fof(f273,plain,
    ( sK2 != k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl5_5
    | spl5_22 ),
    inference(subsumption_resolution,[],[f228,f69])).

fof(f228,plain,
    ( sK2 != k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl5_22 ),
    inference(superposition,[],[f196,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f196,plain,
    ( sK2 != k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f194])).

fof(f272,plain,
    ( ~ spl5_32
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | spl5_21 ),
    inference(avatar_split_clause,[],[f267,f190,f92,f82,f77,f67,f269])).

fof(f190,plain,
    ( spl5_21
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f267,plain,
    ( ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | spl5_21 ),
    inference(subsumption_resolution,[],[f266,f94])).

fof(f266,plain,
    ( ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | spl5_21 ),
    inference(subsumption_resolution,[],[f265,f84])).

fof(f265,plain,
    ( ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl5_5
    | ~ spl5_7
    | spl5_21 ),
    inference(subsumption_resolution,[],[f264,f79])).

fof(f264,plain,
    ( ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl5_5
    | spl5_21 ),
    inference(subsumption_resolution,[],[f227,f69])).

fof(f227,plain,
    ( ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl5_21 ),
    inference(superposition,[],[f192,f43])).

fof(f192,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f190])).

fof(f249,plain,
    ( spl5_29
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f223,f92,f82,f77,f67,f246])).

fof(f223,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f94,f79,f84,f69,f43])).

fof(f197,plain,
    ( ~ spl5_21
    | ~ spl5_22
    | spl5_1 ),
    inference(avatar_split_clause,[],[f168,f47,f194,f190])).

fof(f47,plain,
    ( spl5_1
  <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f168,plain,
    ( sK2 != k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_1 ),
    inference(superposition,[],[f49,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f49,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f188,plain,
    ( spl5_19
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f187,f82,f62,f171])).

fof(f62,plain,
    ( spl5_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f187,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f167,f84])).

fof(f167,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_4 ),
    inference(superposition,[],[f64,f40])).

fof(f64,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f186,plain,
    ( spl5_20
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f185,f67,f57,f177])).

fof(f57,plain,
    ( spl5_3
  <=> sK2 = k2_relset_1(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f185,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f166,f69])).

fof(f166,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_3 ),
    inference(superposition,[],[f59,f40])).

fof(f59,plain,
    ( sK2 = k2_relset_1(sK1,sK2,sK4)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f157,plain,
    ( spl5_18
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f152,f124,f106,f154])).

fof(f124,plain,
    ( spl5_14
  <=> v4_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f152,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1)
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f108,f126,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f126,plain,
    ( v4_relat_1(sK4,sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f124])).

fof(f128,plain,
    ( spl5_14
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f116,f67,f124])).

fof(f116,plain,
    ( v4_relat_1(sK4,sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f41,f69])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f111,plain,
    ( spl5_11
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f99,f82,f101])).

fof(f99,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_8 ),
    inference(resolution,[],[f39,f84])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f110,plain,
    ( spl5_12
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f98,f67,f106])).

fof(f98,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f39,f69])).

fof(f95,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f26,f92])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & k1_xboole_0 != sK2
    & sK2 = k2_relset_1(sK1,sK2,sK4)
    & sK1 = k2_relset_1(sK0,sK1,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
            & k1_xboole_0 != X2
            & k2_relset_1(X1,X2,X4) = X2
            & k2_relset_1(X0,X1,X3) = X1
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & k1_xboole_0 != sK2
          & sK2 = k2_relset_1(sK1,sK2,X4)
          & sK1 = k2_relset_1(sK0,sK1,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X4] :
        ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
        & k1_xboole_0 != sK2
        & sK2 = k2_relset_1(sK1,sK2,X4)
        & sK1 = k2_relset_1(sK0,sK1,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X4,sK1,sK2)
        & v1_funct_1(X4) )
   => ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
      & k1_xboole_0 != sK2
      & sK2 = k2_relset_1(sK1,sK2,sK4)
      & sK1 = k2_relset_1(sK0,sK1,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X1,X2,X4) = X2
                & k2_relset_1(X0,X1,X3) = X1 )
             => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X1,X2,X4) = X2
              & k2_relset_1(X0,X1,X3) = X1 )
           => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_2)).

fof(f85,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f28,f82])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f35,f47])).

fof(f35,plain,(
    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:30:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (17697)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (17686)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (17697)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f351,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f50,f60,f65,f70,f80,f85,f95,f110,f111,f128,f157,f186,f188,f197,f249,f272,f281,f321,f349])).
% 0.21/0.47  fof(f349,plain,(
% 0.21/0.47    ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | ~spl5_29 | spl5_32),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f348])).
% 0.21/0.47  fof(f348,plain,(
% 0.21/0.47    $false | (~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | ~spl5_29 | spl5_32)),
% 0.21/0.47    inference(subsumption_resolution,[],[f347,f271])).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_32),
% 0.21/0.47    inference(avatar_component_clause,[],[f269])).
% 0.21/0.47  fof(f269,plain,(
% 0.21/0.47    spl5_32 <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.47  fof(f347,plain,(
% 0.21/0.47    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | ~spl5_29)),
% 0.21/0.47    inference(forward_demodulation,[],[f327,f248])).
% 0.21/0.47  fof(f248,plain,(
% 0.21/0.47    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | ~spl5_29),
% 0.21/0.47    inference(avatar_component_clause,[],[f246])).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    spl5_29 <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.47  fof(f327,plain,(
% 0.21/0.47    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f94,f79,f84,f69,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl5_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl5_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    v1_funct_1(sK4) | ~spl5_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl5_7 <=> v1_funct_1(sK4)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    v1_funct_1(sK3) | ~spl5_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl5_10 <=> v1_funct_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.47  fof(f321,plain,(
% 0.21/0.47    ~spl5_11 | ~spl5_12 | ~spl5_18 | ~spl5_19 | ~spl5_20 | spl5_33),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f320])).
% 0.21/0.47  fof(f320,plain,(
% 0.21/0.47    $false | (~spl5_11 | ~spl5_12 | ~spl5_18 | ~spl5_19 | ~spl5_20 | spl5_33)),
% 0.21/0.47    inference(subsumption_resolution,[],[f319,f156])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK4),sK1) | ~spl5_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f154])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    spl5_18 <=> r1_tarski(k1_relat_1(sK4),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    ~r1_tarski(k1_relat_1(sK4),sK1) | (~spl5_11 | ~spl5_12 | ~spl5_19 | ~spl5_20 | spl5_33)),
% 0.21/0.47    inference(forward_demodulation,[],[f318,f173])).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    sK1 = k2_relat_1(sK3) | ~spl5_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f171])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    spl5_19 <=> sK1 = k2_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.47  fof(f318,plain,(
% 0.21/0.47    ~r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3)) | (~spl5_11 | ~spl5_12 | ~spl5_20 | spl5_33)),
% 0.21/0.47    inference(subsumption_resolution,[],[f317,f108])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    v1_relat_1(sK4) | ~spl5_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f106])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl5_12 <=> v1_relat_1(sK4)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.47  fof(f317,plain,(
% 0.21/0.47    ~r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3)) | ~v1_relat_1(sK4) | (~spl5_11 | ~spl5_20 | spl5_33)),
% 0.21/0.47    inference(subsumption_resolution,[],[f316,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    v1_relat_1(sK3) | ~spl5_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl5_11 <=> v1_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.47  fof(f316,plain,(
% 0.21/0.47    ~r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK4) | (~spl5_20 | spl5_33)),
% 0.21/0.47    inference(subsumption_resolution,[],[f315,f179])).
% 0.21/0.47  fof(f179,plain,(
% 0.21/0.47    sK2 = k2_relat_1(sK4) | ~spl5_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f177])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    spl5_20 <=> sK2 = k2_relat_1(sK4)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.47  fof(f315,plain,(
% 0.21/0.47    sK2 != k2_relat_1(sK4) | ~r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK4) | spl5_33),
% 0.21/0.47    inference(superposition,[],[f280,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 0.21/0.47  fof(f280,plain,(
% 0.21/0.47    sK2 != k2_relat_1(k5_relat_1(sK3,sK4)) | spl5_33),
% 0.21/0.47    inference(avatar_component_clause,[],[f278])).
% 0.21/0.47  fof(f278,plain,(
% 0.21/0.47    spl5_33 <=> sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    ~spl5_33 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | spl5_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f276,f194,f92,f82,f77,f67,f278])).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    spl5_22 <=> sK2 = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.47  fof(f276,plain,(
% 0.21/0.47    sK2 != k2_relat_1(k5_relat_1(sK3,sK4)) | (~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | spl5_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f275,f94])).
% 0.21/0.47  fof(f275,plain,(
% 0.21/0.47    sK2 != k2_relat_1(k5_relat_1(sK3,sK4)) | ~v1_funct_1(sK3) | (~spl5_5 | ~spl5_7 | ~spl5_8 | spl5_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f274,f84])).
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    sK2 != k2_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | (~spl5_5 | ~spl5_7 | spl5_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f273,f79])).
% 0.21/0.47  fof(f273,plain,(
% 0.21/0.47    sK2 != k2_relat_1(k5_relat_1(sK3,sK4)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | (~spl5_5 | spl5_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f228,f69])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    sK2 != k2_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl5_22),
% 0.21/0.47    inference(superposition,[],[f196,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    sK2 != k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) | spl5_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f194])).
% 0.21/0.47  fof(f272,plain,(
% 0.21/0.47    ~spl5_32 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | spl5_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f267,f190,f92,f82,f77,f67,f269])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    spl5_21 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.47  fof(f267,plain,(
% 0.21/0.47    ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10 | spl5_21)),
% 0.21/0.47    inference(subsumption_resolution,[],[f266,f94])).
% 0.21/0.47  fof(f266,plain,(
% 0.21/0.47    ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | (~spl5_5 | ~spl5_7 | ~spl5_8 | spl5_21)),
% 0.21/0.47    inference(subsumption_resolution,[],[f265,f84])).
% 0.21/0.47  fof(f265,plain,(
% 0.21/0.47    ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | (~spl5_5 | ~spl5_7 | spl5_21)),
% 0.21/0.47    inference(subsumption_resolution,[],[f264,f79])).
% 0.21/0.47  fof(f264,plain,(
% 0.21/0.47    ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | (~spl5_5 | spl5_21)),
% 0.21/0.47    inference(subsumption_resolution,[],[f227,f69])).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl5_21),
% 0.21/0.47    inference(superposition,[],[f192,f43])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f190])).
% 0.21/0.47  fof(f249,plain,(
% 0.21/0.47    spl5_29 | ~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f223,f92,f82,f77,f67,f246])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl5_5 | ~spl5_7 | ~spl5_8 | ~spl5_10)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f94,f79,f84,f69,f43])).
% 0.21/0.47  fof(f197,plain,(
% 0.21/0.47    ~spl5_21 | ~spl5_22 | spl5_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f168,f47,f194,f190])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl5_1 <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    sK2 != k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_1),
% 0.21/0.47    inference(superposition,[],[f49,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    spl5_19 | ~spl5_4 | ~spl5_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f187,f82,f62,f171])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl5_4 <=> sK1 = k2_relset_1(sK0,sK1,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    sK1 = k2_relat_1(sK3) | (~spl5_4 | ~spl5_8)),
% 0.21/0.47    inference(subsumption_resolution,[],[f167,f84])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    sK1 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_4),
% 0.21/0.47    inference(superposition,[],[f64,f40])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    sK1 = k2_relset_1(sK0,sK1,sK3) | ~spl5_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f62])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    spl5_20 | ~spl5_3 | ~spl5_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f185,f67,f57,f177])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl5_3 <=> sK2 = k2_relset_1(sK1,sK2,sK4)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    sK2 = k2_relat_1(sK4) | (~spl5_3 | ~spl5_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f166,f69])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    sK2 = k2_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_3),
% 0.21/0.47    inference(superposition,[],[f59,f40])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    sK2 = k2_relset_1(sK1,sK2,sK4) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl5_18 | ~spl5_12 | ~spl5_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f152,f124,f106,f154])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl5_14 <=> v4_relat_1(sK4,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    r1_tarski(k1_relat_1(sK4),sK1) | (~spl5_12 | ~spl5_14)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f108,f126,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    v4_relat_1(sK4,sK1) | ~spl5_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f124])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl5_14 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f116,f67,f124])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    v4_relat_1(sK4,sK1) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f41,f69])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl5_11 | ~spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f99,f82,f101])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl5_8),
% 0.21/0.48    inference(resolution,[],[f39,f84])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl5_12 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f67,f106])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    v1_relat_1(sK4) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f39,f69])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl5_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f92])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,sK4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f11,f23,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,X4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X4] : (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,X4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) => (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,sK4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2) & (k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_2)).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl5_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f82])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f77])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v1_funct_1(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f67])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f62])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    sK1 = k2_relset_1(sK0,sK1,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f57])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    sK2 = k2_relset_1(sK1,sK2,sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f47])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17697)------------------------------
% 0.21/0.48  % (17697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17697)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17697)Memory used [KB]: 10874
% 0.21/0.48  % (17697)Time elapsed: 0.055 s
% 0.21/0.48  % (17697)------------------------------
% 0.21/0.48  % (17697)------------------------------
% 0.21/0.48  % (17680)Success in time 0.119 s
%------------------------------------------------------------------------------
