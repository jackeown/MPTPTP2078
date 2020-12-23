%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 284 expanded)
%              Number of leaves         :   41 ( 135 expanded)
%              Depth                    :    7
%              Number of atoms          :  507 ( 875 expanded)
%              Number of equality atoms :   38 (  67 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f364,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f117,f122,f127,f136,f140,f146,f156,f161,f168,f173,f178,f188,f193,f213,f214,f261,f283,f293,f307,f347,f352,f363])).

fof(f363,plain,
    ( ~ spl4_8
    | ~ spl4_14
    | ~ spl4_35
    | ~ spl4_42 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_14
    | ~ spl4_35
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f121,f155,f345,f282])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v2_funct_2(sK1,X0)
        | ~ v5_relat_1(sK1,X0) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl4_35
  <=> ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v2_funct_2(sK1,X0)
        | ~ v5_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f345,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl4_42
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f155,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_14
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f121,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_8
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f352,plain,
    ( spl4_9
    | spl4_42 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | spl4_9
    | spl4_42 ),
    inference(unit_resulting_resolution,[],[f126,f69,f346,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP3(X1,X0) ) ),
    inference(cnf_transformation,[],[f72_D])).

fof(f72_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP3(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).

fof(f346,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | spl4_42 ),
    inference(avatar_component_clause,[],[f344])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f44,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f126,plain,
    ( ~ sP3(sK0,sK0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_9
  <=> sP3(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f347,plain,
    ( ~ spl4_10
    | ~ spl4_12
    | ~ spl4_1
    | ~ spl4_42
    | ~ spl4_16
    | spl4_38 ),
    inference(avatar_split_clause,[],[f309,f304,f165,f344,f75,f143,f129])).

fof(f129,plain,
    ( spl4_10
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f143,plain,
    ( spl4_12
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f75,plain,
    ( spl4_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f165,plain,
    ( spl4_16
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f304,plain,
    ( spl4_38
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f309,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_16
    | spl4_38 ),
    inference(forward_demodulation,[],[f308,f167])).

fof(f167,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f308,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_38 ),
    inference(superposition,[],[f306,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f306,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f304])).

fof(f307,plain,
    ( ~ spl4_1
    | ~ spl4_23
    | ~ spl4_19
    | ~ spl4_4
    | ~ spl4_38
    | spl4_36 ),
    inference(avatar_split_clause,[],[f294,f290,f304,f90,f185,f206,f75])).

fof(f206,plain,
    ( spl4_23
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f185,plain,
    ( spl4_19
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f90,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f290,plain,
    ( spl4_36
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f294,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl4_36 ),
    inference(superposition,[],[f292,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f292,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl4_36 ),
    inference(avatar_component_clause,[],[f290])).

fof(f293,plain,
    ( ~ spl4_36
    | spl4_7
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f284,f175,f114,f290])).

fof(f114,plain,
    ( spl4_7
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f175,plain,
    ( spl4_18
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f284,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl4_7
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f116,f177])).

fof(f177,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f116,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f283,plain,
    ( ~ spl4_10
    | spl4_35
    | spl4_31 ),
    inference(avatar_split_clause,[],[f262,f258,f281,f129])).

fof(f258,plain,
    ( spl4_31
  <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f262,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v5_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1)
        | ~ v2_funct_2(sK1,X0) )
    | spl4_31 ),
    inference(superposition,[],[f260,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f260,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f258])).

fof(f261,plain,
    ( ~ spl4_10
    | ~ spl4_12
    | ~ spl4_1
    | ~ spl4_31
    | spl4_24 ),
    inference(avatar_split_clause,[],[f235,f210,f258,f75,f143,f129])).

fof(f210,plain,
    ( spl4_24
  <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f235,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl4_24 ),
    inference(superposition,[],[f212,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f212,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f210])).

fof(f214,plain,
    ( ~ spl4_1
    | ~ spl4_4
    | ~ spl4_3
    | ~ spl4_2
    | spl4_23
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f183,f175,f206,f80,f85,f90,f75])).

fof(f85,plain,
    ( spl4_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f80,plain,
    ( spl4_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f183,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl4_18 ),
    inference(superposition,[],[f59,f177])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f213,plain,
    ( ~ spl4_19
    | ~ spl4_4
    | ~ spl4_1
    | ~ spl4_23
    | ~ spl4_24
    | spl4_20 ),
    inference(avatar_split_clause,[],[f194,f190,f210,f206,f75,f90,f185])).

fof(f190,plain,
    ( spl4_20
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f194,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | spl4_20 ),
    inference(superposition,[],[f192,f67])).

fof(f192,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f193,plain,
    ( ~ spl4_20
    | spl4_6
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f180,f175,f110,f190])).

fof(f110,plain,
    ( spl4_6
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f180,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl4_6
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f112,f177])).

fof(f112,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f188,plain,
    ( spl4_19
    | ~ spl4_17
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f179,f175,f170,f185])).

fof(f170,plain,
    ( spl4_17
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

% (26076)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (26081)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f179,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl4_17
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f172,f177])).

fof(f172,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f178,plain,
    ( spl4_18
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f102,f90,f80,f85,f75,f175])).

fof(f102,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f173,plain,
    ( spl4_17
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f101,f90,f80,f85,f75,f170])).

fof(f101,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k2_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f168,plain,
    ( ~ spl4_4
    | spl4_16
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f162,f158,f165,f90])).

fof(f158,plain,
    ( spl4_15
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f162,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_15 ),
    inference(superposition,[],[f160,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f160,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f158])).

fof(f161,plain,
    ( spl4_15
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f100,f90,f80,f75,f158])).

fof(f100,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f156,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f95,f90,f75,f85,f153])).

fof(f95,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_2(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

% (26077)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f146,plain,
    ( spl4_12
    | ~ spl4_3
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f94,f90,f75,f85,f143])).

fof(f94,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f140,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f52,f135])).

fof(f135,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_11
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f136,plain,
    ( spl4_10
    | ~ spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f103,f90,f133,f129])).

fof(f103,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f127,plain,
    ( ~ spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f99,f90,f124])).

fof(f99,plain,
    ( ~ sP3(sK0,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP3(X1,X0) ) ),
    inference(general_splitting,[],[f66,f72_D])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f122,plain,
    ( spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f97,f90,f119])).

fof(f97,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f117,plain,
    ( ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f68,f114,f110])).

fof(f68,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f39,f44,f44])).

fof(f39,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f93,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f42,f85])).

fof(f42,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f80])).

fof(f41,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f40,f75])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:24:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (26073)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (26065)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (26061)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (26064)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (26063)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (26082)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (26083)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (26058)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (26074)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (26066)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (26059)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (26062)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (26078)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (26082)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (26068)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (26070)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (26072)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (26071)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (26086)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (26087)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (26089)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (26079)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (26084)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (26069)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f364,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f117,f122,f127,f136,f140,f146,f156,f161,f168,f173,f178,f188,f193,f213,f214,f261,f283,f293,f307,f347,f352,f363])).
% 0.20/0.54  fof(f363,plain,(
% 0.20/0.54    ~spl4_8 | ~spl4_14 | ~spl4_35 | ~spl4_42),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f361])).
% 0.20/0.54  fof(f361,plain,(
% 0.20/0.54    $false | (~spl4_8 | ~spl4_14 | ~spl4_35 | ~spl4_42)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f121,f155,f345,f282])).
% 0.20/0.54  fof(f282,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0)) ) | ~spl4_35),
% 0.20/0.54    inference(avatar_component_clause,[],[f281])).
% 0.20/0.54  fof(f281,plain,(
% 0.20/0.54    spl4_35 <=> ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.54  fof(f345,plain,(
% 0.20/0.54    r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~spl4_42),
% 0.20/0.54    inference(avatar_component_clause,[],[f344])).
% 0.20/0.54  fof(f344,plain,(
% 0.20/0.54    spl4_42 <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    v2_funct_2(sK1,sK0) | ~spl4_14),
% 0.20/0.54    inference(avatar_component_clause,[],[f153])).
% 0.20/0.54  fof(f153,plain,(
% 0.20/0.54    spl4_14 <=> v2_funct_2(sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    v5_relat_1(sK1,sK0) | ~spl4_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f119])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    spl4_8 <=> v5_relat_1(sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.54  fof(f352,plain,(
% 0.20/0.54    spl4_9 | spl4_42),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f349])).
% 0.20/0.54  fof(f349,plain,(
% 0.20/0.54    $false | (spl4_9 | spl4_42)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f126,f69,f346,f72])).
% 0.20/0.54  fof(f72,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP3(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f72_D])).
% 0.20/0.54  fof(f72_D,plain,(
% 0.20/0.54    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP3(X1,X0)) )),
% 0.20/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.54  fof(f346,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | spl4_42),
% 0.20/0.54    inference(avatar_component_clause,[],[f344])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f46,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    ~sP3(sK0,sK0) | spl4_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f124])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    spl4_9 <=> sP3(sK0,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.54  fof(f347,plain,(
% 0.20/0.54    ~spl4_10 | ~spl4_12 | ~spl4_1 | ~spl4_42 | ~spl4_16 | spl4_38),
% 0.20/0.54    inference(avatar_split_clause,[],[f309,f304,f165,f344,f75,f143,f129])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    spl4_10 <=> v1_relat_1(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    spl4_12 <=> v2_funct_1(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    spl4_1 <=> v1_funct_1(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.54  fof(f165,plain,(
% 0.20/0.54    spl4_16 <=> sK0 = k1_relat_1(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.54  fof(f304,plain,(
% 0.20/0.54    spl4_38 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.54  fof(f309,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl4_16 | spl4_38)),
% 0.20/0.54    inference(forward_demodulation,[],[f308,f167])).
% 0.20/0.54  fof(f167,plain,(
% 0.20/0.54    sK0 = k1_relat_1(sK1) | ~spl4_16),
% 0.20/0.54    inference(avatar_component_clause,[],[f165])).
% 0.20/0.54  fof(f308,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_38),
% 0.20/0.54    inference(superposition,[],[f306,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.54  fof(f306,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl4_38),
% 0.20/0.54    inference(avatar_component_clause,[],[f304])).
% 0.20/0.54  fof(f307,plain,(
% 0.20/0.54    ~spl4_1 | ~spl4_23 | ~spl4_19 | ~spl4_4 | ~spl4_38 | spl4_36),
% 0.20/0.54    inference(avatar_split_clause,[],[f294,f290,f304,f90,f185,f206,f75])).
% 0.20/0.54  fof(f206,plain,(
% 0.20/0.54    spl4_23 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.54  fof(f185,plain,(
% 0.20/0.54    spl4_19 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.54  fof(f290,plain,(
% 0.20/0.54    spl4_36 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.54  fof(f294,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl4_36),
% 0.20/0.54    inference(superposition,[],[f292,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.54    inference(flattening,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.54  fof(f292,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl4_36),
% 0.20/0.54    inference(avatar_component_clause,[],[f290])).
% 0.20/0.54  fof(f293,plain,(
% 0.20/0.54    ~spl4_36 | spl4_7 | ~spl4_18),
% 0.20/0.54    inference(avatar_split_clause,[],[f284,f175,f114,f290])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    spl4_7 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.54  fof(f175,plain,(
% 0.20/0.54    spl4_18 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.54  fof(f284,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | (spl4_7 | ~spl4_18)),
% 0.20/0.54    inference(forward_demodulation,[],[f116,f177])).
% 0.20/0.54  fof(f177,plain,(
% 0.20/0.54    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl4_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f175])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | spl4_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f114])).
% 0.20/0.54  fof(f283,plain,(
% 0.20/0.54    ~spl4_10 | spl4_35 | spl4_31),
% 0.20/0.54    inference(avatar_split_clause,[],[f262,f258,f281,f129])).
% 0.20/0.54  fof(f258,plain,(
% 0.20/0.54    spl4_31 <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.20/0.54  fof(f262,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v5_relat_1(sK1,X0) | ~v1_relat_1(sK1) | ~v2_funct_2(sK1,X0)) ) | spl4_31),
% 0.20/0.54    inference(superposition,[],[f260,f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v2_funct_2(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.20/0.54  fof(f260,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | spl4_31),
% 0.20/0.54    inference(avatar_component_clause,[],[f258])).
% 0.20/0.54  fof(f261,plain,(
% 0.20/0.54    ~spl4_10 | ~spl4_12 | ~spl4_1 | ~spl4_31 | spl4_24),
% 0.20/0.54    inference(avatar_split_clause,[],[f235,f210,f258,f75,f143,f129])).
% 0.20/0.54  fof(f210,plain,(
% 0.20/0.54    spl4_24 <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.54  fof(f235,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | spl4_24),
% 0.20/0.54    inference(superposition,[],[f212,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f212,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl4_24),
% 0.20/0.54    inference(avatar_component_clause,[],[f210])).
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    ~spl4_1 | ~spl4_4 | ~spl4_3 | ~spl4_2 | spl4_23 | ~spl4_18),
% 0.20/0.54    inference(avatar_split_clause,[],[f183,f175,f206,f80,f85,f90,f75])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    spl4_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.54  fof(f80,plain,(
% 0.20/0.54    spl4_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.54  fof(f183,plain,(
% 0.20/0.54    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~spl4_18),
% 0.20/0.54    inference(superposition,[],[f59,f177])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.54    inference(flattening,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.20/0.54  fof(f213,plain,(
% 0.20/0.54    ~spl4_19 | ~spl4_4 | ~spl4_1 | ~spl4_23 | ~spl4_24 | spl4_20),
% 0.20/0.54    inference(avatar_split_clause,[],[f194,f190,f210,f206,f75,f90,f185])).
% 0.20/0.54  fof(f190,plain,(
% 0.20/0.54    spl4_20 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.54  fof(f194,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | spl4_20),
% 0.20/0.54    inference(superposition,[],[f192,f67])).
% 0.20/0.54  fof(f192,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl4_20),
% 0.20/0.54    inference(avatar_component_clause,[],[f190])).
% 0.20/0.54  fof(f193,plain,(
% 0.20/0.54    ~spl4_20 | spl4_6 | ~spl4_18),
% 0.20/0.54    inference(avatar_split_clause,[],[f180,f175,f110,f190])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    spl4_6 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.54  fof(f180,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | (spl4_6 | ~spl4_18)),
% 0.20/0.54    inference(backward_demodulation,[],[f112,f177])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | spl4_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f110])).
% 0.20/0.54  fof(f188,plain,(
% 0.20/0.54    spl4_19 | ~spl4_17 | ~spl4_18),
% 0.20/0.54    inference(avatar_split_clause,[],[f179,f175,f170,f185])).
% 0.20/0.54  fof(f170,plain,(
% 0.20/0.54    spl4_17 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.54  % (26076)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (26081)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  fof(f179,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_1(sK1)) | (~spl4_17 | ~spl4_18)),
% 0.20/0.54    inference(backward_demodulation,[],[f172,f177])).
% 0.20/0.54  fof(f172,plain,(
% 0.20/0.54    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl4_17),
% 0.20/0.54    inference(avatar_component_clause,[],[f170])).
% 0.20/0.54  fof(f178,plain,(
% 0.20/0.54    spl4_18 | ~spl4_1 | ~spl4_3 | ~spl4_2 | ~spl4_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f102,f90,f80,f85,f75,f175])).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl4_4),
% 0.20/0.54    inference(resolution,[],[f92,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.54    inference(flattening,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f90])).
% 0.20/0.54  fof(f173,plain,(
% 0.20/0.54    spl4_17 | ~spl4_1 | ~spl4_3 | ~spl4_2 | ~spl4_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f101,f90,f80,f85,f75,f170])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl4_4),
% 0.20/0.54    inference(resolution,[],[f92,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | v1_funct_1(k2_funct_2(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f28])).
% 0.20/0.54  fof(f168,plain,(
% 0.20/0.54    ~spl4_4 | spl4_16 | ~spl4_15),
% 0.20/0.54    inference(avatar_split_clause,[],[f162,f158,f165,f90])).
% 0.20/0.54  fof(f158,plain,(
% 0.20/0.54    spl4_15 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.54  fof(f162,plain,(
% 0.20/0.54    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_15),
% 0.20/0.54    inference(superposition,[],[f160,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl4_15),
% 0.20/0.54    inference(avatar_component_clause,[],[f158])).
% 0.20/0.54  fof(f161,plain,(
% 0.20/0.54    spl4_15 | ~spl4_1 | ~spl4_2 | ~spl4_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f100,f90,f80,f75,f158])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl4_4),
% 0.20/0.54    inference(resolution,[],[f92,f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.54    inference(flattening,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    spl4_14 | ~spl4_3 | ~spl4_1 | ~spl4_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f95,f90,f75,f85,f153])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_2(sK1,sK0) | ~spl4_4),
% 0.20/0.54    inference(resolution,[],[f92,f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f33])).
% 0.20/0.54  % (26077)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.20/0.54  fof(f146,plain,(
% 0.20/0.54    spl4_12 | ~spl4_3 | ~spl4_1 | ~spl4_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f94,f90,f75,f85,f143])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_1(sK1) | ~spl4_4),
% 0.20/0.54    inference(resolution,[],[f92,f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f140,plain,(
% 0.20/0.54    spl4_11),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f137])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    $false | spl4_11),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f52,f135])).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl4_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f133])).
% 0.20/0.54  fof(f133,plain,(
% 0.20/0.54    spl4_11 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    spl4_10 | ~spl4_11 | ~spl4_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f103,f90,f133,f129])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK1) | ~spl4_4),
% 0.20/0.54    inference(resolution,[],[f92,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    ~spl4_9 | ~spl4_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f99,f90,f124])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    ~sP3(sK0,sK0) | ~spl4_4),
% 0.20/0.54    inference(resolution,[],[f92,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP3(X1,X0)) )),
% 0.20/0.54    inference(general_splitting,[],[f66,f72_D])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    spl4_8 | ~spl4_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f97,f90,f119])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    v5_relat_1(sK1,sK0) | ~spl4_4),
% 0.20/0.54    inference(resolution,[],[f92,f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    ~spl4_6 | ~spl4_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f68,f114,f110])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 0.20/0.54    inference(definition_unfolding,[],[f39,f44,f44])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.54    inference(flattening,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.20/0.54    inference(negated_conjecture,[],[f16])).
% 0.20/0.54  fof(f16,conjecture,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    spl4_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f43,f90])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    spl4_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f42,f85])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    v3_funct_2(sK1,sK0,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f83,plain,(
% 0.20/0.54    spl4_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f41,f80])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    spl4_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f40,f75])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    v1_funct_1(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (26082)------------------------------
% 0.20/0.54  % (26082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26082)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (26082)Memory used [KB]: 11001
% 0.20/0.54  % (26082)Time elapsed: 0.129 s
% 0.20/0.54  % (26082)------------------------------
% 0.20/0.54  % (26082)------------------------------
% 0.20/0.55  % (26088)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (26075)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (26057)Success in time 0.188 s
%------------------------------------------------------------------------------
