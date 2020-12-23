%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0980+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:00 EST 2020

% Result     : Theorem 35.58s
% Output     : Refutation 36.67s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 223 expanded)
%              Number of leaves         :   37 ( 102 expanded)
%              Depth                    :    7
%              Number of atoms          :  426 (1117 expanded)
%              Number of equality atoms :   65 ( 194 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63934,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4736,f4743,f4747,f4751,f4755,f4759,f4763,f4771,f6697,f14204,f20238,f21767,f25130,f25132,f25461,f25499,f25654,f27018,f39045,f61178,f63120,f63811,f63933])).

fof(f63933,plain,
    ( sK6 != k1_relset_1(sK6,sK7,sK9)
    | k1_relat_1(sK9) != k1_relset_1(sK6,sK7,sK9)
    | r1_tarski(k2_relat_1(sK8),k1_relat_1(sK9))
    | ~ r1_tarski(k2_relat_1(sK8),sK6) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f63811,plain,
    ( ~ spl303_45
    | ~ spl303_7
    | ~ spl303_11
    | ~ spl303_10
    | ~ spl303_8544
    | spl303_1
    | ~ spl303_1327 ),
    inference(avatar_split_clause,[],[f63772,f14725,f4734,f63809,f4769,f4804,f4757,f5236])).

fof(f5236,plain,
    ( spl303_45
  <=> v1_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_45])])).

fof(f4757,plain,
    ( spl303_7
  <=> v1_funct_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_7])])).

fof(f4804,plain,
    ( spl303_11
  <=> v1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_11])])).

fof(f4769,plain,
    ( spl303_10
  <=> v1_funct_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_10])])).

fof(f63809,plain,
    ( spl303_8544
  <=> r1_tarski(k2_relat_1(sK8),k1_relat_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_8544])])).

fof(f4734,plain,
    ( spl303_1
  <=> v2_funct_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_1])])).

fof(f14725,plain,
    ( spl303_1327
  <=> v2_funct_1(k5_relat_1(sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_1327])])).

fof(f63772,plain,
    ( v2_funct_1(sK8)
    | ~ r1_tarski(k2_relat_1(sK8),k1_relat_1(sK9))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9)
    | ~ spl303_1327 ),
    inference(resolution,[],[f14726,f3080])).

fof(f3080,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1576])).

fof(f1576,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1575])).

fof(f1575,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1018])).

fof(f1018,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(f14726,plain,
    ( v2_funct_1(k5_relat_1(sK8,sK9))
    | ~ spl303_1327 ),
    inference(avatar_component_clause,[],[f14725])).

fof(f63120,plain,(
    spl303_1268 ),
    inference(avatar_contradiction_clause,[],[f63102])).

fof(f63102,plain,
    ( $false
    | spl303_1268 ),
    inference(resolution,[],[f13092,f3178])).

fof(f3178,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f13092,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | spl303_1268 ),
    inference(avatar_component_clause,[],[f13091])).

fof(f13091,plain,
    ( spl303_1268
  <=> v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_1268])])).

fof(f61178,plain,(
    spl303_887 ),
    inference(avatar_contradiction_clause,[],[f61160])).

fof(f61160,plain,
    ( $false
    | spl303_887 ),
    inference(resolution,[],[f9920,f3178])).

fof(f9920,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK6,sK7))
    | spl303_887 ),
    inference(avatar_component_clause,[],[f9919])).

fof(f9919,plain,
    ( spl303_887
  <=> v1_relat_1(k2_zfmisc_1(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_887])])).

fof(f39045,plain,
    ( ~ spl303_11
    | spl303_5110
    | ~ spl303_1206 ),
    inference(avatar_split_clause,[],[f39003,f12828,f39043,f4804])).

fof(f39043,plain,
    ( spl303_5110
  <=> r1_tarski(k2_relat_1(sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_5110])])).

fof(f12828,plain,
    ( spl303_1206
  <=> v5_relat_1(sK8,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_1206])])).

fof(f39003,plain,
    ( r1_tarski(k2_relat_1(sK8),sK6)
    | ~ v1_relat_1(sK8)
    | ~ spl303_1206 ),
    inference(resolution,[],[f12829,f3996])).

fof(f3996,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2796])).

fof(f2796,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f2214])).

fof(f2214,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f12829,plain,
    ( v5_relat_1(sK8,sK6)
    | ~ spl303_1206 ),
    inference(avatar_component_clause,[],[f12828])).

fof(f27018,plain,(
    spl303_2194 ),
    inference(avatar_contradiction_clause,[],[f26775])).

fof(f26775,plain,
    ( $false
    | spl303_2194 ),
    inference(resolution,[],[f21766,f3923])).

fof(f3923,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f21766,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl303_2194 ),
    inference(avatar_component_clause,[],[f21765])).

fof(f21765,plain,
    ( spl303_2194
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_2194])])).

fof(f25654,plain,
    ( ~ spl303_10
    | ~ spl303_8
    | ~ spl303_7
    | ~ spl303_5
    | spl303_1327
    | ~ spl303_4 ),
    inference(avatar_split_clause,[],[f25634,f4745,f14725,f4749,f4757,f4761,f4769])).

fof(f4761,plain,
    ( spl303_8
  <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_8])])).

fof(f4749,plain,
    ( spl303_5
  <=> m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_5])])).

fof(f4745,plain,
    ( spl303_4
  <=> v2_funct_1(k1_partfun1(sK5,sK6,sK6,sK7,sK8,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_4])])).

fof(f25634,plain,
    ( v2_funct_1(k5_relat_1(sK8,sK9))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ v1_funct_1(sK9)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ spl303_4 ),
    inference(superposition,[],[f4746,f3115])).

fof(f3115,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f1600])).

fof(f1600,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f1599])).

fof(f1599,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f1485])).

fof(f1485,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f4746,plain,
    ( v2_funct_1(k1_partfun1(sK5,sK6,sK6,sK7,sK8,sK9))
    | ~ spl303_4 ),
    inference(avatar_component_clause,[],[f4745])).

fof(f25499,plain,
    ( spl303_1206
    | ~ spl303_8 ),
    inference(avatar_split_clause,[],[f25311,f4761,f12828])).

fof(f25311,plain,
    ( v5_relat_1(sK8,sK6)
    | ~ spl303_8 ),
    inference(resolution,[],[f4762,f3968])).

fof(f3968,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2203])).

fof(f2203,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f1211,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f4762,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ spl303_8 ),
    inference(avatar_component_clause,[],[f4761])).

fof(f25461,plain,
    ( ~ spl303_791
    | spl303_34
    | ~ spl303_8 ),
    inference(avatar_split_clause,[],[f25275,f4761,f4896,f9515])).

fof(f9515,plain,
    ( spl303_791
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_791])])).

fof(f4896,plain,
    ( spl303_34
  <=> v1_xboole_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_34])])).

fof(f25275,plain,
    ( v1_xboole_0(sK8)
    | ~ v1_xboole_0(sK6)
    | ~ spl303_8 ),
    inference(resolution,[],[f4762,f3894])).

fof(f3894,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2152])).

fof(f2152,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1213])).

fof(f1213,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f25132,plain,
    ( spl303_831
    | ~ spl303_5 ),
    inference(avatar_split_clause,[],[f24950,f4749,f9682])).

fof(f9682,plain,
    ( spl303_831
  <=> k1_relat_1(sK9) = k1_relset_1(sK6,sK7,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_831])])).

fof(f24950,plain,
    ( k1_relat_1(sK9) = k1_relset_1(sK6,sK7,sK9)
    | ~ spl303_5 ),
    inference(resolution,[],[f4750,f4254])).

fof(f4254,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2326])).

fof(f2326,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f4750,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ spl303_5 ),
    inference(avatar_component_clause,[],[f4749])).

fof(f25130,plain,
    ( spl303_2
    | ~ spl303_6
    | spl303_577
    | ~ spl303_5 ),
    inference(avatar_split_clause,[],[f24947,f4749,f7782,f4753,f4738])).

fof(f4738,plain,
    ( spl303_2
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_2])])).

fof(f4753,plain,
    ( spl303_6
  <=> v1_funct_2(sK9,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_6])])).

fof(f7782,plain,
    ( spl303_577
  <=> sK6 = k1_relset_1(sK6,sK7,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_577])])).

fof(f24947,plain,
    ( sK6 = k1_relset_1(sK6,sK7,sK9)
    | ~ v1_funct_2(sK9,sK6,sK7)
    | k1_xboole_0 = sK7
    | ~ spl303_5 ),
    inference(resolution,[],[f4750,f4247])).

fof(f4247,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2908])).

fof(f2908,plain,(
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
    inference(nnf_transformation,[],[f2324])).

fof(f2324,plain,(
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
    inference(flattening,[],[f2323])).

fof(f2323,plain,(
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
    inference(ennf_transformation,[],[f1472])).

fof(f1472,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f21767,plain,
    ( ~ spl303_2194
    | ~ spl303_3
    | spl303_791 ),
    inference(avatar_split_clause,[],[f21763,f9515,f4741,f21765])).

fof(f4741,plain,
    ( spl303_3
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl303_3])])).

fof(f21763,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl303_3
    | spl303_791 ),
    inference(forward_demodulation,[],[f9516,f4742])).

fof(f4742,plain,
    ( k1_xboole_0 = sK6
    | ~ spl303_3 ),
    inference(avatar_component_clause,[],[f4741])).

fof(f9516,plain,
    ( ~ v1_xboole_0(sK6)
    | spl303_791 ),
    inference(avatar_component_clause,[],[f9515])).

fof(f20238,plain,
    ( ~ spl303_1268
    | spl303_11
    | ~ spl303_8 ),
    inference(avatar_split_clause,[],[f20048,f4761,f4804,f13091])).

fof(f20048,plain,
    ( v1_relat_1(sK8)
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | ~ spl303_8 ),
    inference(resolution,[],[f4762,f3148])).

fof(f3148,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1623])).

fof(f1623,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f14204,plain,
    ( ~ spl303_887
    | spl303_45
    | ~ spl303_5 ),
    inference(avatar_split_clause,[],[f14018,f4749,f5236,f9919])).

fof(f14018,plain,
    ( v1_relat_1(sK9)
    | ~ v1_relat_1(k2_zfmisc_1(sK6,sK7))
    | ~ spl303_5 ),
    inference(resolution,[],[f4750,f3148])).

fof(f6697,plain,
    ( ~ spl303_34
    | ~ spl303_11
    | spl303_1
    | ~ spl303_10 ),
    inference(avatar_split_clause,[],[f6406,f4769,f4734,f4804,f4896])).

fof(f6406,plain,
    ( v2_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ v1_xboole_0(sK8)
    | ~ spl303_10 ),
    inference(resolution,[],[f4770,f3109])).

fof(f3109,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1596])).

fof(f1596,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1595])).

fof(f1595,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f891])).

fof(f891,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f4770,plain,
    ( v1_funct_1(sK8)
    | ~ spl303_10 ),
    inference(avatar_component_clause,[],[f4769])).

fof(f4771,plain,(
    spl303_10 ),
    inference(avatar_split_clause,[],[f3002,f4769])).

fof(f3002,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f2438])).

fof(f2438,plain,
    ( ~ v2_funct_1(sK8)
    & ( k1_xboole_0 = sK6
      | k1_xboole_0 != sK7 )
    & v2_funct_1(k1_partfun1(sK5,sK6,sK6,sK7,sK8,sK9))
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK9,sK6,sK7)
    & v1_funct_1(sK9)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f1529,f2437,f2436])).

fof(f2436,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ v2_funct_1(X3)
            & ( k1_xboole_0 = X1
              | k1_xboole_0 != X2 )
            & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ v2_funct_1(sK8)
          & ( k1_xboole_0 = sK6
            | k1_xboole_0 != sK7 )
          & v2_funct_1(k1_partfun1(sK5,sK6,sK6,sK7,sK8,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
          & v1_funct_2(X4,sK6,sK7)
          & v1_funct_1(X4) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK8,sK5,sK6)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f2437,plain,
    ( ? [X4] :
        ( ~ v2_funct_1(sK8)
        & ( k1_xboole_0 = sK6
          | k1_xboole_0 != sK7 )
        & v2_funct_1(k1_partfun1(sK5,sK6,sK6,sK7,sK8,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
        & v1_funct_2(X4,sK6,sK7)
        & v1_funct_1(X4) )
   => ( ~ v2_funct_1(sK8)
      & ( k1_xboole_0 = sK6
        | k1_xboole_0 != sK7 )
      & v2_funct_1(k1_partfun1(sK5,sK6,sK6,sK7,sK8,sK9))
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_2(sK9,sK6,sK7)
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f1529,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1528])).

fof(f1528,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1500])).

fof(f1500,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
             => ( v2_funct_1(X3)
                | ( k1_xboole_0 != X1
                  & k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1499])).

fof(f1499,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f4763,plain,(
    spl303_8 ),
    inference(avatar_split_clause,[],[f3004,f4761])).

fof(f3004,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f2438])).

fof(f4759,plain,(
    spl303_7 ),
    inference(avatar_split_clause,[],[f3005,f4757])).

fof(f3005,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f2438])).

fof(f4755,plain,(
    spl303_6 ),
    inference(avatar_split_clause,[],[f3006,f4753])).

fof(f3006,plain,(
    v1_funct_2(sK9,sK6,sK7) ),
    inference(cnf_transformation,[],[f2438])).

fof(f4751,plain,(
    spl303_5 ),
    inference(avatar_split_clause,[],[f3007,f4749])).

fof(f3007,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f2438])).

fof(f4747,plain,(
    spl303_4 ),
    inference(avatar_split_clause,[],[f3008,f4745])).

fof(f3008,plain,(
    v2_funct_1(k1_partfun1(sK5,sK6,sK6,sK7,sK8,sK9)) ),
    inference(cnf_transformation,[],[f2438])).

fof(f4743,plain,
    ( ~ spl303_2
    | spl303_3 ),
    inference(avatar_split_clause,[],[f3009,f4741,f4738])).

fof(f3009,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f2438])).

fof(f4736,plain,(
    ~ spl303_1 ),
    inference(avatar_split_clause,[],[f3010,f4734])).

fof(f3010,plain,(
    ~ v2_funct_1(sK8) ),
    inference(cnf_transformation,[],[f2438])).
%------------------------------------------------------------------------------
