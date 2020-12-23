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
% DateTime   : Thu Dec  3 13:05:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 277 expanded)
%              Number of leaves         :   39 ( 132 expanded)
%              Depth                    :    7
%              Number of atoms          :  493 ( 859 expanded)
%              Number of equality atoms :   38 (  67 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f109,f118,f128,f133,f139,f149,f154,f161,f166,f171,f181,f186,f206,f207,f254,f276,f286,f309,f341,f343,f348])).

fof(f348,plain,
    ( ~ spl4_9
    | ~ spl4_13
    | ~ spl4_34
    | ~ spl4_41 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_34
    | ~ spl4_41 ),
    inference(unit_resulting_resolution,[],[f127,f148,f339,f275])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v2_funct_2(sK1,X0)
        | ~ v5_relat_1(sK1,X0) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl4_34
  <=> ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v2_funct_2(sK1,X0)
        | ~ v5_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f339,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl4_41
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f148,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl4_13
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f127,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_9
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f343,plain,
    ( spl4_10
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | spl4_10
    | spl4_41 ),
    inference(unit_resulting_resolution,[],[f132,f70,f340,f73])).

% (6099)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP3(X1,X0) ) ),
    inference(cnf_transformation,[],[f73_D])).

fof(f73_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP3(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f340,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f338])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f45,f43])).

fof(f43,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f132,plain,
    ( ~ sP3(sK0,sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_10
  <=> sP3(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f341,plain,
    ( ~ spl4_5
    | ~ spl4_11
    | ~ spl4_1
    | ~ spl4_41
    | ~ spl4_15
    | spl4_39 ),
    inference(avatar_split_clause,[],[f325,f306,f158,f338,f76,f136,f106])).

fof(f106,plain,
    ( spl4_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f136,plain,
    ( spl4_11
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f76,plain,
    ( spl4_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f158,plain,
    ( spl4_15
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f306,plain,
    ( spl4_39
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f325,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_15
    | spl4_39 ),
    inference(forward_demodulation,[],[f324,f160])).

fof(f160,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f324,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_39 ),
    inference(superposition,[],[f308,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f308,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f306])).

fof(f309,plain,
    ( ~ spl4_1
    | ~ spl4_22
    | ~ spl4_19
    | ~ spl4_4
    | ~ spl4_39
    | spl4_35 ),
    inference(avatar_split_clause,[],[f287,f283,f306,f91,f183,f199,f76])).

fof(f199,plain,
    ( spl4_22
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f183,plain,
    ( spl4_19
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f91,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f283,plain,
    ( spl4_35
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f287,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl4_35 ),
    inference(superposition,[],[f285,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f285,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f283])).

fof(f286,plain,
    ( ~ spl4_35
    | spl4_7
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f277,f168,f115,f283])).

fof(f115,plain,
    ( spl4_7
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f168,plain,
    ( spl4_17
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f277,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl4_7
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f117,f170])).

fof(f170,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f117,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f276,plain,
    ( ~ spl4_5
    | spl4_34
    | spl4_30 ),
    inference(avatar_split_clause,[],[f255,f251,f274,f106])).

fof(f251,plain,
    ( spl4_30
  <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v5_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1)
        | ~ v2_funct_2(sK1,X0) )
    | spl4_30 ),
    inference(superposition,[],[f253,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f253,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f251])).

% (6106)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f254,plain,
    ( ~ spl4_5
    | ~ spl4_11
    | ~ spl4_1
    | ~ spl4_30
    | spl4_23 ),
    inference(avatar_split_clause,[],[f233,f203,f251,f76,f136,f106])).

fof(f203,plain,
    ( spl4_23
  <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f233,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_23 ),
    inference(superposition,[],[f205,f47])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f205,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f203])).

fof(f207,plain,
    ( ~ spl4_1
    | ~ spl4_4
    | ~ spl4_3
    | ~ spl4_2
    | spl4_22
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f176,f168,f199,f81,f86,f91,f76])).

fof(f86,plain,
    ( spl4_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f81,plain,
    ( spl4_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f176,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl4_17 ),
    inference(superposition,[],[f54,f170])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

% (6123)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f206,plain,
    ( ~ spl4_19
    | ~ spl4_4
    | ~ spl4_1
    | ~ spl4_22
    | ~ spl4_23
    | spl4_18 ),
    inference(avatar_split_clause,[],[f187,f178,f203,f199,f76,f91,f183])).

fof(f178,plain,
    ( spl4_18
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f187,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | spl4_18 ),
    inference(superposition,[],[f180,f68])).

fof(f180,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f178])).

fof(f186,plain,
    ( spl4_19
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f172,f168,f163,f183])).

fof(f163,plain,
    ( spl4_16
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f172,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl4_16
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f165,f170])).

fof(f165,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f181,plain,
    ( ~ spl4_18
    | spl4_6
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f173,f168,f111,f178])).

fof(f111,plain,
    ( spl4_6
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f173,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl4_6
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f113,f170])).

fof(f113,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f171,plain,
    ( spl4_17
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f104,f91,f81,f86,f76,f168])).

fof(f104,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f166,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f103,f91,f81,f86,f76,f163])).

fof(f103,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f161,plain,
    ( ~ spl4_4
    | spl4_15
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f155,f151,f158,f91])).

fof(f151,plain,
    ( spl4_14
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f155,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_14 ),
    inference(superposition,[],[f153,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f153,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f154,plain,
    ( spl4_14
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f102,f91,f81,f76,f151])).

fof(f102,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

% (6100)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f149,plain,
    ( spl4_13
    | ~ spl4_3
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f99,f91,f76,f86,f146])).

fof(f99,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_2(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

% (6124)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

% (6107)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f139,plain,
    ( spl4_11
    | ~ spl4_3
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f98,f91,f76,f86,f136])).

fof(f98,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f133,plain,
    ( ~ spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f101,f91,f130])).

fof(f101,plain,
    ( ~ sP3(sK0,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP3(X1,X0) ) ),
    inference(general_splitting,[],[f67,f73_D])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f128,plain,
    ( spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f97,f91,f125])).

fof(f97,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f118,plain,
    ( ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f69,f115,f111])).

fof(f69,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f38,f43,f43])).

fof(f38,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f109,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f95,f91,f106])).

fof(f95,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f94,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f41,f86])).

fof(f41,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (6101)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (6118)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (6109)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (6096)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (6108)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (6098)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (6118)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (6117)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (6097)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (6102)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (6120)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f349,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f109,f118,f128,f133,f139,f149,f154,f161,f166,f171,f181,f186,f206,f207,f254,f276,f286,f309,f341,f343,f348])).
% 0.21/0.55  fof(f348,plain,(
% 0.21/0.55    ~spl4_9 | ~spl4_13 | ~spl4_34 | ~spl4_41),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f346])).
% 0.21/0.55  fof(f346,plain,(
% 0.21/0.55    $false | (~spl4_9 | ~spl4_13 | ~spl4_34 | ~spl4_41)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f127,f148,f339,f275])).
% 0.21/0.55  fof(f275,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0)) ) | ~spl4_34),
% 0.21/0.55    inference(avatar_component_clause,[],[f274])).
% 0.21/0.55  fof(f274,plain,(
% 0.21/0.55    spl4_34 <=> ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.55  fof(f339,plain,(
% 0.21/0.55    r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~spl4_41),
% 0.21/0.55    inference(avatar_component_clause,[],[f338])).
% 0.21/0.55  fof(f338,plain,(
% 0.21/0.55    spl4_41 <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    v2_funct_2(sK1,sK0) | ~spl4_13),
% 0.21/0.55    inference(avatar_component_clause,[],[f146])).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    spl4_13 <=> v2_funct_2(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    v5_relat_1(sK1,sK0) | ~spl4_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f125])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    spl4_9 <=> v5_relat_1(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.55  fof(f343,plain,(
% 0.21/0.55    spl4_10 | spl4_41),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f342])).
% 0.21/0.55  fof(f342,plain,(
% 0.21/0.55    $false | (spl4_10 | spl4_41)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f132,f70,f340,f73])).
% 0.21/0.55  % (6099)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP3(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f73_D])).
% 0.21/0.55  fof(f73_D,plain,(
% 0.21/0.55    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP3(X1,X0)) )),
% 0.21/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.55  fof(f340,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | spl4_41),
% 0.21/0.55    inference(avatar_component_clause,[],[f338])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f45,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    ~sP3(sK0,sK0) | spl4_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f130])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    spl4_10 <=> sP3(sK0,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.55  fof(f341,plain,(
% 0.21/0.55    ~spl4_5 | ~spl4_11 | ~spl4_1 | ~spl4_41 | ~spl4_15 | spl4_39),
% 0.21/0.55    inference(avatar_split_clause,[],[f325,f306,f158,f338,f76,f136,f106])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    spl4_5 <=> v1_relat_1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    spl4_11 <=> v2_funct_1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    spl4_1 <=> v1_funct_1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    spl4_15 <=> sK0 = k1_relat_1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.55  fof(f306,plain,(
% 0.21/0.55    spl4_39 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.55  fof(f325,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_15 | spl4_39)),
% 0.21/0.55    inference(forward_demodulation,[],[f324,f160])).
% 0.21/0.55  fof(f160,plain,(
% 0.21/0.55    sK0 = k1_relat_1(sK1) | ~spl4_15),
% 0.21/0.55    inference(avatar_component_clause,[],[f158])).
% 0.21/0.55  fof(f324,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_39),
% 0.21/0.55    inference(superposition,[],[f308,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(flattening,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.55  fof(f308,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl4_39),
% 0.21/0.55    inference(avatar_component_clause,[],[f306])).
% 0.21/0.55  fof(f309,plain,(
% 0.21/0.55    ~spl4_1 | ~spl4_22 | ~spl4_19 | ~spl4_4 | ~spl4_39 | spl4_35),
% 0.21/0.55    inference(avatar_split_clause,[],[f287,f283,f306,f91,f183,f199,f76])).
% 0.21/0.55  fof(f199,plain,(
% 0.21/0.55    spl4_22 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.55  fof(f183,plain,(
% 0.21/0.55    spl4_19 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.55  fof(f283,plain,(
% 0.21/0.55    spl4_35 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.55  fof(f287,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl4_35),
% 0.21/0.55    inference(superposition,[],[f285,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.55    inference(flattening,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.55  fof(f285,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl4_35),
% 0.21/0.55    inference(avatar_component_clause,[],[f283])).
% 0.21/0.55  fof(f286,plain,(
% 0.21/0.55    ~spl4_35 | spl4_7 | ~spl4_17),
% 0.21/0.55    inference(avatar_split_clause,[],[f277,f168,f115,f283])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    spl4_7 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    spl4_17 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.55  fof(f277,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | (spl4_7 | ~spl4_17)),
% 0.21/0.55    inference(forward_demodulation,[],[f117,f170])).
% 0.21/0.55  fof(f170,plain,(
% 0.21/0.55    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl4_17),
% 0.21/0.55    inference(avatar_component_clause,[],[f168])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | spl4_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f115])).
% 0.21/0.55  fof(f276,plain,(
% 0.21/0.55    ~spl4_5 | spl4_34 | spl4_30),
% 0.21/0.55    inference(avatar_split_clause,[],[f255,f251,f274,f106])).
% 0.21/0.55  fof(f251,plain,(
% 0.21/0.55    spl4_30 <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.55  fof(f255,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v5_relat_1(sK1,X0) | ~v1_relat_1(sK1) | ~v2_funct_2(sK1,X0)) ) | spl4_30),
% 0.21/0.55    inference(superposition,[],[f253,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v2_funct_2(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.21/0.55  fof(f253,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | spl4_30),
% 0.21/0.55    inference(avatar_component_clause,[],[f251])).
% 0.21/0.55  % (6106)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  fof(f254,plain,(
% 0.21/0.55    ~spl4_5 | ~spl4_11 | ~spl4_1 | ~spl4_30 | spl4_23),
% 0.21/0.55    inference(avatar_split_clause,[],[f233,f203,f251,f76,f136,f106])).
% 0.21/0.55  fof(f203,plain,(
% 0.21/0.55    spl4_23 <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.55  fof(f233,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_23),
% 0.21/0.55    inference(superposition,[],[f205,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f205,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl4_23),
% 0.21/0.55    inference(avatar_component_clause,[],[f203])).
% 0.21/0.55  fof(f207,plain,(
% 0.21/0.55    ~spl4_1 | ~spl4_4 | ~spl4_3 | ~spl4_2 | spl4_22 | ~spl4_17),
% 0.21/0.55    inference(avatar_split_clause,[],[f176,f168,f199,f81,f86,f91,f76])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    spl4_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    spl4_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~spl4_17),
% 0.21/0.55    inference(superposition,[],[f54,f170])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  % (6123)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.55    inference(flattening,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    ~spl4_19 | ~spl4_4 | ~spl4_1 | ~spl4_22 | ~spl4_23 | spl4_18),
% 0.21/0.55    inference(avatar_split_clause,[],[f187,f178,f203,f199,f76,f91,f183])).
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    spl4_18 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | spl4_18),
% 0.21/0.55    inference(superposition,[],[f180,f68])).
% 0.21/0.55  fof(f180,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl4_18),
% 0.21/0.55    inference(avatar_component_clause,[],[f178])).
% 0.21/0.55  fof(f186,plain,(
% 0.21/0.55    spl4_19 | ~spl4_16 | ~spl4_17),
% 0.21/0.55    inference(avatar_split_clause,[],[f172,f168,f163,f183])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    spl4_16 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    v1_funct_1(k2_funct_1(sK1)) | (~spl4_16 | ~spl4_17)),
% 0.21/0.55    inference(backward_demodulation,[],[f165,f170])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl4_16),
% 0.21/0.55    inference(avatar_component_clause,[],[f163])).
% 0.21/0.55  fof(f181,plain,(
% 0.21/0.55    ~spl4_18 | spl4_6 | ~spl4_17),
% 0.21/0.55    inference(avatar_split_clause,[],[f173,f168,f111,f178])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    spl4_6 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.55  fof(f173,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | (spl4_6 | ~spl4_17)),
% 0.21/0.55    inference(backward_demodulation,[],[f113,f170])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | spl4_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f111])).
% 0.21/0.55  fof(f171,plain,(
% 0.21/0.55    spl4_17 | ~spl4_1 | ~spl4_3 | ~spl4_2 | ~spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f104,f91,f81,f86,f76,f168])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f93,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f91])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    spl4_16 | ~spl4_1 | ~spl4_3 | ~spl4_2 | ~spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f103,f91,f81,f86,f76,f163])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f93,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    ~spl4_4 | spl4_15 | ~spl4_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f155,f151,f158,f91])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    spl4_14 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_14),
% 0.21/0.55    inference(superposition,[],[f153,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl4_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f151])).
% 0.21/0.55  fof(f154,plain,(
% 0.21/0.55    spl4_14 | ~spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f102,f91,f81,f76,f151])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f93,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  % (6100)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.55    inference(flattening,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    spl4_13 | ~spl4_3 | ~spl4_1 | ~spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f99,f91,f76,f86,f146])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_2(sK1,sK0) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f93,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(flattening,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  % (6124)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.21/0.55  % (6107)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    spl4_11 | ~spl4_3 | ~spl4_1 | ~spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f98,f91,f76,f86,f136])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_1(sK1) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f93,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    ~spl4_10 | ~spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f101,f91,f130])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ~sP3(sK0,sK0) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f93,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP3(X1,X0)) )),
% 0.21/0.55    inference(general_splitting,[],[f67,f73_D])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(flattening,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    spl4_9 | ~spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f97,f91,f125])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    v5_relat_1(sK1,sK0) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f93,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    ~spl4_6 | ~spl4_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f69,f115,f111])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.21/0.55    inference(definition_unfolding,[],[f38,f43,f43])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.55    inference(negated_conjecture,[],[f15])).
% 0.21/0.55  fof(f15,conjecture,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    spl4_5 | ~spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f95,f91,f106])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f93,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    spl4_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f42,f91])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    spl4_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f41,f86])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    v3_funct_2(sK1,sK0,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    spl4_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f40,f81])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    spl4_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f39,f76])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    v1_funct_1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (6118)------------------------------
% 0.21/0.55  % (6118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6118)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (6118)Memory used [KB]: 11001
% 0.21/0.55  % (6118)Time elapsed: 0.112 s
% 0.21/0.55  % (6118)------------------------------
% 0.21/0.55  % (6118)------------------------------
% 0.21/0.55  % (6095)Success in time 0.182 s
%------------------------------------------------------------------------------
