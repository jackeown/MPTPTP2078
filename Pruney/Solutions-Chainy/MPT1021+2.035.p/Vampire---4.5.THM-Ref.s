%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:55 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 281 expanded)
%              Number of leaves         :   38 ( 131 expanded)
%              Depth                    :    9
%              Number of atoms          :  516 ( 943 expanded)
%              Number of equality atoms :   46 (  75 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f107,f116,f121,f131,f137,f142,f149,f154,f171,f181,f186,f202,f207,f258,f261,f271,f277,f283,f301,f304])).

fof(f304,plain,
    ( ~ spl2_8
    | ~ spl2_11
    | ~ spl2_31
    | ~ spl2_37 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_31
    | ~ spl2_37 ),
    inference(unit_resulting_resolution,[],[f136,f120,f256,f300])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v5_relat_1(sK1,X0)
        | ~ v2_funct_2(sK1,X0) )
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl2_37
  <=> ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v5_relat_1(sK1,X0)
        | ~ v2_funct_2(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f256,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl2_31
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f120,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl2_8
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f136,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl2_11
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f301,plain,
    ( ~ spl2_5
    | spl2_37
    | spl2_34 ),
    inference(avatar_split_clause,[],[f284,f280,f299,f104])).

fof(f104,plain,
    ( spl2_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f280,plain,
    ( spl2_34
  <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0))
        | ~ v2_funct_2(sK1,X0)
        | ~ v5_relat_1(sK1,X0)
        | ~ v1_relat_1(sK1) )
    | spl2_34 ),
    inference(superposition,[],[f282,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f282,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | spl2_34 ),
    inference(avatar_component_clause,[],[f280])).

fof(f283,plain,
    ( ~ spl2_5
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_34
    | spl2_33 ),
    inference(avatar_split_clause,[],[f278,f274,f280,f128,f75,f104])).

fof(f75,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f128,plain,
    ( spl2_10
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f274,plain,
    ( spl2_33
  <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f278,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_33 ),
    inference(superposition,[],[f276,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f276,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_33 ),
    inference(avatar_component_clause,[],[f274])).

fof(f277,plain,
    ( ~ spl2_18
    | ~ spl2_22
    | ~ spl2_1
    | ~ spl2_4
    | ~ spl2_33
    | spl2_32 ),
    inference(avatar_split_clause,[],[f272,f268,f274,f90,f75,f199,f178])).

fof(f178,plain,
    ( spl2_18
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f199,plain,
    ( spl2_22
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f90,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f268,plain,
    ( spl2_32
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f272,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | spl2_32 ),
    inference(superposition,[],[f270,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f270,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_32 ),
    inference(avatar_component_clause,[],[f268])).

fof(f271,plain,
    ( ~ spl2_32
    | spl2_7
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f262,f168,f113,f268])).

fof(f113,plain,
    ( spl2_7
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f168,plain,
    ( spl2_17
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f262,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))
    | spl2_7
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f115,f170])).

fof(f170,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f115,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f261,plain,(
    spl2_31 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl2_31 ),
    inference(unit_resulting_resolution,[],[f70,f257,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f257,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | spl2_31 ),
    inference(avatar_component_clause,[],[f255])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f48,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f258,plain,
    ( ~ spl2_5
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_31
    | ~ spl2_13
    | spl2_23 ),
    inference(avatar_split_clause,[],[f234,f204,f146,f255,f128,f75,f104])).

fof(f146,plain,
    ( spl2_13
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f204,plain,
    ( spl2_23
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f234,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl2_13
    | spl2_23 ),
    inference(forward_demodulation,[],[f233,f148])).

fof(f148,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f233,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl2_23 ),
    inference(superposition,[],[f206,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f206,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_23 ),
    inference(avatar_component_clause,[],[f204])).

fof(f207,plain,
    ( ~ spl2_1
    | ~ spl2_4
    | ~ spl2_18
    | ~ spl2_22
    | ~ spl2_23
    | spl2_19 ),
    inference(avatar_split_clause,[],[f187,f183,f204,f199,f178,f90,f75])).

fof(f183,plain,
    ( spl2_19
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f187,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl2_19 ),
    inference(superposition,[],[f185,f68])).

fof(f185,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f183])).

fof(f202,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_22
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f176,f168,f199,f90,f85,f80,f75])).

fof(f80,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( spl2_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f176,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl2_17 ),
    inference(superposition,[],[f58,f170])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f186,plain,
    ( ~ spl2_19
    | spl2_6
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f173,f168,f109,f183])).

fof(f109,plain,
    ( spl2_6
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f173,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))
    | spl2_6
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f111,f170])).

fof(f111,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f181,plain,
    ( spl2_18
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f172,f168,f151,f178])).

fof(f151,plain,
    ( spl2_14
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f172,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f153,f170])).

fof(f153,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f171,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_17
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f96,f90,f168,f85,f80,f75])).

fof(f96,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f92,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

% (1604)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f154,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_14
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f95,f90,f151,f85,f80,f75])).

fof(f95,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f92,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | v1_funct_1(k2_funct_2(X0,X1))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f149,plain,
    ( ~ spl2_4
    | spl2_13
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f143,f139,f146,f90])).

fof(f139,plain,
    ( spl2_12
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f143,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_12 ),
    inference(superposition,[],[f141,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f141,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f142,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_12
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f94,f90,f139,f80,f75])).

fof(f94,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f92,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f137,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f100,f90,f85,f75,f134])).

fof(f100,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f92,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
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

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f131,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f99,f90,f85,f75,f128])).

fof(f99,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f92,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f121,plain,
    ( spl2_8
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f101,f90,f118])).

fof(f101,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f92,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f116,plain,
    ( ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f69,f113,f109])).

fof(f69,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f47,f48,f48])).

fof(f47,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f39])).

fof(f39,plain,
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(f107,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f102,f90,f104])).

fof(f102,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f92,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f93,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f46,f90])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f45,f85])).

fof(f45,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f44,f80])).

fof(f44,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f43,f75])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.54  % (1607)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (1621)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (1619)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (1615)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.26/0.55  % (1629)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.26/0.55  % (1627)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.26/0.55  % (1613)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.26/0.55  % (1611)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.26/0.55  % (1623)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.26/0.56  % (1611)Refutation found. Thanks to Tanya!
% 1.26/0.56  % SZS status Theorem for theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f305,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f107,f116,f121,f131,f137,f142,f149,f154,f171,f181,f186,f202,f207,f258,f261,f271,f277,f283,f301,f304])).
% 1.53/0.57  fof(f304,plain,(
% 1.53/0.57    ~spl2_8 | ~spl2_11 | ~spl2_31 | ~spl2_37),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f302])).
% 1.53/0.57  fof(f302,plain,(
% 1.53/0.57    $false | (~spl2_8 | ~spl2_11 | ~spl2_31 | ~spl2_37)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f136,f120,f256,f300])).
% 1.53/0.57  fof(f300,plain,(
% 1.53/0.57    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v5_relat_1(sK1,X0) | ~v2_funct_2(sK1,X0)) ) | ~spl2_37),
% 1.53/0.57    inference(avatar_component_clause,[],[f299])).
% 1.53/0.57  fof(f299,plain,(
% 1.53/0.57    spl2_37 <=> ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v5_relat_1(sK1,X0) | ~v2_funct_2(sK1,X0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 1.53/0.57  fof(f256,plain,(
% 1.53/0.57    r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~spl2_31),
% 1.53/0.57    inference(avatar_component_clause,[],[f255])).
% 1.53/0.57  fof(f255,plain,(
% 1.53/0.57    spl2_31 <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 1.53/0.57  fof(f120,plain,(
% 1.53/0.57    v5_relat_1(sK1,sK0) | ~spl2_8),
% 1.53/0.57    inference(avatar_component_clause,[],[f118])).
% 1.53/0.57  fof(f118,plain,(
% 1.53/0.57    spl2_8 <=> v5_relat_1(sK1,sK0)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.53/0.57  fof(f136,plain,(
% 1.53/0.57    v2_funct_2(sK1,sK0) | ~spl2_11),
% 1.53/0.57    inference(avatar_component_clause,[],[f134])).
% 1.53/0.57  fof(f134,plain,(
% 1.53/0.57    spl2_11 <=> v2_funct_2(sK1,sK0)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.53/0.57  fof(f301,plain,(
% 1.53/0.57    ~spl2_5 | spl2_37 | spl2_34),
% 1.53/0.57    inference(avatar_split_clause,[],[f284,f280,f299,f104])).
% 1.53/0.57  fof(f104,plain,(
% 1.53/0.57    spl2_5 <=> v1_relat_1(sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.53/0.57  fof(f280,plain,(
% 1.53/0.57    spl2_34 <=> r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 1.53/0.57  fof(f284,plain,(
% 1.53/0.57    ( ! [X0] : (~r2_relset_1(sK0,sK0,k6_relat_1(X0),k6_relat_1(sK0)) | ~v2_funct_2(sK1,X0) | ~v5_relat_1(sK1,X0) | ~v1_relat_1(sK1)) ) | spl2_34),
% 1.53/0.57    inference(superposition,[],[f282,f52])).
% 1.53/0.57  fof(f52,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f41])).
% 1.53/0.57  fof(f41,plain,(
% 1.53/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.53/0.57    inference(nnf_transformation,[],[f23])).
% 1.53/0.57  fof(f23,plain,(
% 1.53/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.53/0.57    inference(flattening,[],[f22])).
% 1.53/0.57  fof(f22,plain,(
% 1.53/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.53/0.57    inference(ennf_transformation,[],[f7])).
% 1.53/0.57  fof(f7,axiom,(
% 1.53/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.53/0.57  fof(f282,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | spl2_34),
% 1.53/0.57    inference(avatar_component_clause,[],[f280])).
% 1.53/0.57  fof(f283,plain,(
% 1.53/0.57    ~spl2_5 | ~spl2_1 | ~spl2_10 | ~spl2_34 | spl2_33),
% 1.53/0.57    inference(avatar_split_clause,[],[f278,f274,f280,f128,f75,f104])).
% 1.53/0.57  fof(f75,plain,(
% 1.53/0.57    spl2_1 <=> v1_funct_1(sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.53/0.57  fof(f128,plain,(
% 1.53/0.57    spl2_10 <=> v2_funct_1(sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.53/0.57  fof(f274,plain,(
% 1.53/0.57    spl2_33 <=> r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 1.53/0.57  fof(f278,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k6_relat_1(k2_relat_1(sK1)),k6_relat_1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_33),
% 1.53/0.57    inference(superposition,[],[f276,f51])).
% 1.53/0.57  fof(f51,plain,(
% 1.53/0.57    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f21])).
% 1.53/0.57  fof(f21,plain,(
% 1.53/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.57    inference(flattening,[],[f20])).
% 1.53/0.57  fof(f20,plain,(
% 1.53/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.53/0.57  fof(f276,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl2_33),
% 1.53/0.57    inference(avatar_component_clause,[],[f274])).
% 1.53/0.57  fof(f277,plain,(
% 1.53/0.57    ~spl2_18 | ~spl2_22 | ~spl2_1 | ~spl2_4 | ~spl2_33 | spl2_32),
% 1.53/0.57    inference(avatar_split_clause,[],[f272,f268,f274,f90,f75,f199,f178])).
% 1.53/0.57  fof(f178,plain,(
% 1.53/0.57    spl2_18 <=> v1_funct_1(k2_funct_1(sK1))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.53/0.57  fof(f199,plain,(
% 1.53/0.57    spl2_22 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.53/0.57  fof(f90,plain,(
% 1.53/0.57    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.53/0.57  fof(f268,plain,(
% 1.53/0.57    spl2_32 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 1.53/0.57  fof(f272,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k5_relat_1(k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | spl2_32),
% 1.53/0.57    inference(superposition,[],[f270,f68])).
% 1.53/0.57  fof(f68,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f38])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.53/0.57    inference(flattening,[],[f37])).
% 1.53/0.57  fof(f37,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.53/0.57    inference(ennf_transformation,[],[f10])).
% 1.53/0.57  fof(f10,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.53/0.57  fof(f270,plain,(
% 1.53/0.57    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | spl2_32),
% 1.53/0.57    inference(avatar_component_clause,[],[f268])).
% 1.53/0.57  fof(f271,plain,(
% 1.53/0.57    ~spl2_32 | spl2_7 | ~spl2_17),
% 1.53/0.57    inference(avatar_split_clause,[],[f262,f168,f113,f268])).
% 1.53/0.57  fof(f113,plain,(
% 1.53/0.57    spl2_7 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.53/0.58  fof(f168,plain,(
% 1.53/0.58    spl2_17 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.53/0.58  fof(f262,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_relat_1(sK0)) | (spl2_7 | ~spl2_17)),
% 1.53/0.58    inference(forward_demodulation,[],[f115,f170])).
% 1.53/0.58  fof(f170,plain,(
% 1.53/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl2_17),
% 1.53/0.58    inference(avatar_component_clause,[],[f168])).
% 1.53/0.58  fof(f115,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | spl2_7),
% 1.53/0.58    inference(avatar_component_clause,[],[f113])).
% 1.53/0.58  fof(f261,plain,(
% 1.53/0.58    spl2_31),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f260])).
% 1.53/0.58  fof(f260,plain,(
% 1.53/0.58    $false | spl2_31),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f70,f257,f73])).
% 1.53/0.58  fof(f73,plain,(
% 1.53/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.53/0.58    inference(duplicate_literal_removal,[],[f72])).
% 1.53/0.58  fof(f72,plain,(
% 1.53/0.58    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.58    inference(equality_resolution,[],[f67])).
% 1.53/0.58  fof(f67,plain,(
% 1.53/0.58    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f42])).
% 1.53/0.58  fof(f42,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(nnf_transformation,[],[f36])).
% 1.53/0.58  fof(f36,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(flattening,[],[f35])).
% 1.53/0.58  fof(f35,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.53/0.58    inference(ennf_transformation,[],[f5])).
% 1.53/0.58  fof(f5,axiom,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.53/0.58  fof(f257,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | spl2_31),
% 1.53/0.58    inference(avatar_component_clause,[],[f255])).
% 1.53/0.58  fof(f70,plain,(
% 1.53/0.58    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.53/0.58    inference(definition_unfolding,[],[f49,f48])).
% 1.53/0.58  fof(f48,plain,(
% 1.53/0.58    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f12])).
% 1.53/0.58  fof(f12,axiom,(
% 1.53/0.58    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.53/0.58  fof(f49,plain,(
% 1.53/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f16])).
% 1.53/0.58  fof(f16,plain,(
% 1.53/0.58    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.53/0.58    inference(pure_predicate_removal,[],[f9])).
% 1.53/0.58  fof(f9,axiom,(
% 1.53/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.53/0.58  fof(f258,plain,(
% 1.53/0.58    ~spl2_5 | ~spl2_1 | ~spl2_10 | ~spl2_31 | ~spl2_13 | spl2_23),
% 1.53/0.58    inference(avatar_split_clause,[],[f234,f204,f146,f255,f128,f75,f104])).
% 1.53/0.58  fof(f146,plain,(
% 1.53/0.58    spl2_13 <=> sK0 = k1_relat_1(sK1)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.53/0.58  fof(f204,plain,(
% 1.53/0.58    spl2_23 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 1.53/0.58  fof(f234,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl2_13 | spl2_23)),
% 1.53/0.58    inference(forward_demodulation,[],[f233,f148])).
% 1.53/0.58  fof(f148,plain,(
% 1.53/0.58    sK0 = k1_relat_1(sK1) | ~spl2_13),
% 1.53/0.58    inference(avatar_component_clause,[],[f146])).
% 1.53/0.58  fof(f233,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k6_relat_1(k1_relat_1(sK1)),k6_relat_1(sK0)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl2_23),
% 1.53/0.58    inference(superposition,[],[f206,f50])).
% 1.53/0.58  fof(f50,plain,(
% 1.53/0.58    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f21])).
% 1.53/0.58  fof(f206,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl2_23),
% 1.53/0.58    inference(avatar_component_clause,[],[f204])).
% 1.53/0.58  fof(f207,plain,(
% 1.53/0.58    ~spl2_1 | ~spl2_4 | ~spl2_18 | ~spl2_22 | ~spl2_23 | spl2_19),
% 1.53/0.58    inference(avatar_split_clause,[],[f187,f183,f204,f199,f178,f90,f75])).
% 1.53/0.58  fof(f183,plain,(
% 1.53/0.58    spl2_19 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.53/0.58  fof(f187,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k5_relat_1(sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(k2_funct_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl2_19),
% 1.53/0.58    inference(superposition,[],[f185,f68])).
% 1.53/0.58  fof(f185,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | spl2_19),
% 1.53/0.58    inference(avatar_component_clause,[],[f183])).
% 1.53/0.58  fof(f202,plain,(
% 1.53/0.58    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_22 | ~spl2_17),
% 1.53/0.58    inference(avatar_split_clause,[],[f176,f168,f199,f90,f85,f80,f75])).
% 1.53/0.58  fof(f80,plain,(
% 1.53/0.58    spl2_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.53/0.58  fof(f85,plain,(
% 1.53/0.58    spl2_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.53/0.58  fof(f176,plain,(
% 1.53/0.58    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl2_17),
% 1.53/0.58    inference(superposition,[],[f58,f170])).
% 1.53/0.58  fof(f58,plain,(
% 1.53/0.58    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f27])).
% 1.53/0.58  fof(f27,plain,(
% 1.53/0.58    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.53/0.58    inference(flattening,[],[f26])).
% 1.53/0.58  fof(f26,plain,(
% 1.53/0.58    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f8])).
% 1.53/0.58  fof(f8,axiom,(
% 1.53/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 1.53/0.58  fof(f186,plain,(
% 1.53/0.58    ~spl2_19 | spl2_6 | ~spl2_17),
% 1.53/0.58    inference(avatar_split_clause,[],[f173,f168,f109,f183])).
% 1.53/0.58  fof(f109,plain,(
% 1.53/0.58    spl2_6 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.53/0.58  fof(f173,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_relat_1(sK0)) | (spl2_6 | ~spl2_17)),
% 1.53/0.58    inference(backward_demodulation,[],[f111,f170])).
% 1.53/0.58  fof(f111,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0)) | spl2_6),
% 1.53/0.58    inference(avatar_component_clause,[],[f109])).
% 1.53/0.58  fof(f181,plain,(
% 1.53/0.58    spl2_18 | ~spl2_14 | ~spl2_17),
% 1.53/0.58    inference(avatar_split_clause,[],[f172,f168,f151,f178])).
% 1.53/0.58  fof(f151,plain,(
% 1.53/0.58    spl2_14 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.53/0.58  fof(f172,plain,(
% 1.53/0.58    v1_funct_1(k2_funct_1(sK1)) | (~spl2_14 | ~spl2_17)),
% 1.53/0.58    inference(backward_demodulation,[],[f153,f170])).
% 1.53/0.58  fof(f153,plain,(
% 1.53/0.58    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl2_14),
% 1.53/0.58    inference(avatar_component_clause,[],[f151])).
% 1.53/0.58  fof(f171,plain,(
% 1.53/0.58    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_17 | ~spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f96,f90,f168,f85,f80,f75])).
% 1.53/0.58  fof(f96,plain,(
% 1.53/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl2_4),
% 1.53/0.58    inference(resolution,[],[f92,f54])).
% 1.53/0.58  fof(f54,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f25])).
% 1.53/0.58  fof(f25,plain,(
% 1.53/0.58    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.53/0.58    inference(flattening,[],[f24])).
% 1.53/0.58  fof(f24,plain,(
% 1.53/0.58    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f11])).
% 1.53/0.58  % (1604)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.53/0.58  fof(f11,axiom,(
% 1.53/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.53/0.58  fof(f92,plain,(
% 1.53/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_4),
% 1.53/0.58    inference(avatar_component_clause,[],[f90])).
% 1.53/0.58  fof(f154,plain,(
% 1.53/0.58    ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_14 | ~spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f95,f90,f151,f85,f80,f75])).
% 1.53/0.58  fof(f95,plain,(
% 1.53/0.58    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl2_4),
% 1.53/0.58    inference(resolution,[],[f92,f55])).
% 1.53/0.58  fof(f55,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | v1_funct_1(k2_funct_2(X0,X1)) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f27])).
% 1.53/0.58  fof(f149,plain,(
% 1.53/0.58    ~spl2_4 | spl2_13 | ~spl2_12),
% 1.53/0.58    inference(avatar_split_clause,[],[f143,f139,f146,f90])).
% 1.53/0.58  fof(f139,plain,(
% 1.53/0.58    spl2_12 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.53/0.58  fof(f143,plain,(
% 1.53/0.58    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_12),
% 1.53/0.58    inference(superposition,[],[f141,f61])).
% 1.53/0.58  fof(f61,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  fof(f31,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f4])).
% 1.53/0.58  fof(f4,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.53/0.58  fof(f141,plain,(
% 1.53/0.58    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl2_12),
% 1.53/0.58    inference(avatar_component_clause,[],[f139])).
% 1.53/0.58  fof(f142,plain,(
% 1.53/0.58    ~spl2_1 | ~spl2_2 | spl2_12 | ~spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f94,f90,f139,f80,f75])).
% 1.53/0.58  fof(f94,plain,(
% 1.53/0.58    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl2_4),
% 1.53/0.58    inference(resolution,[],[f92,f59])).
% 1.53/0.58  fof(f59,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f29])).
% 1.53/0.58  fof(f29,plain,(
% 1.53/0.58    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.53/0.58    inference(flattening,[],[f28])).
% 1.53/0.58  fof(f28,plain,(
% 1.53/0.58    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f13])).
% 1.53/0.58  fof(f13,axiom,(
% 1.53/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 1.53/0.58  fof(f137,plain,(
% 1.53/0.58    spl2_11 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f100,f90,f85,f75,f134])).
% 1.53/0.58  fof(f100,plain,(
% 1.53/0.58    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0) | ~spl2_4),
% 1.53/0.58    inference(resolution,[],[f92,f65])).
% 1.53/0.58  fof(f65,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f34])).
% 1.53/0.58  fof(f34,plain,(
% 1.53/0.58    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(flattening,[],[f33])).
% 1.53/0.58  fof(f33,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f6])).
% 1.53/0.58  fof(f6,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.53/0.58  fof(f131,plain,(
% 1.53/0.58    spl2_10 | ~spl2_1 | ~spl2_3 | ~spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f99,f90,f85,f75,f128])).
% 1.53/0.58  fof(f99,plain,(
% 1.53/0.58    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1) | ~spl2_4),
% 1.53/0.58    inference(resolution,[],[f92,f64])).
% 1.53/0.58  fof(f64,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f34])).
% 1.53/0.58  fof(f121,plain,(
% 1.53/0.58    spl2_8 | ~spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f101,f90,f118])).
% 1.53/0.58  fof(f101,plain,(
% 1.53/0.58    v5_relat_1(sK1,sK0) | ~spl2_4),
% 1.53/0.58    inference(resolution,[],[f92,f62])).
% 1.53/0.58  fof(f62,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f32])).
% 1.53/0.58  fof(f32,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f17])).
% 1.53/0.58  fof(f17,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.53/0.58    inference(pure_predicate_removal,[],[f3])).
% 1.53/0.58  fof(f3,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.53/0.58  fof(f116,plain,(
% 1.53/0.58    ~spl2_6 | ~spl2_7),
% 1.53/0.58    inference(avatar_split_clause,[],[f69,f113,f109])).
% 1.53/0.58  fof(f69,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_relat_1(sK0))),
% 1.53/0.58    inference(definition_unfolding,[],[f47,f48,f48])).
% 1.53/0.58  fof(f47,plain,(
% 1.53/0.58    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 1.53/0.58    inference(cnf_transformation,[],[f40])).
% 1.53/0.58  fof(f40,plain,(
% 1.53/0.58    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f39])).
% 1.53/0.58  fof(f39,plain,(
% 1.53/0.58    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f19,plain,(
% 1.53/0.58    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.53/0.58    inference(flattening,[],[f18])).
% 1.53/0.58  fof(f18,plain,(
% 1.53/0.58    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f15])).
% 1.53/0.58  fof(f15,negated_conjecture,(
% 1.53/0.58    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.53/0.58    inference(negated_conjecture,[],[f14])).
% 1.53/0.58  fof(f14,conjecture,(
% 1.53/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).
% 1.53/0.58  fof(f107,plain,(
% 1.53/0.58    spl2_5 | ~spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f102,f90,f104])).
% 1.53/0.58  fof(f102,plain,(
% 1.53/0.58    v1_relat_1(sK1) | ~spl2_4),
% 1.53/0.58    inference(resolution,[],[f92,f60])).
% 1.53/0.58  fof(f60,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f30])).
% 1.53/0.58  fof(f30,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f2])).
% 1.53/0.58  fof(f2,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.53/0.58  fof(f93,plain,(
% 1.53/0.58    spl2_4),
% 1.53/0.58    inference(avatar_split_clause,[],[f46,f90])).
% 1.53/0.58  fof(f46,plain,(
% 1.53/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.53/0.58    inference(cnf_transformation,[],[f40])).
% 1.53/0.58  fof(f88,plain,(
% 1.53/0.58    spl2_3),
% 1.53/0.58    inference(avatar_split_clause,[],[f45,f85])).
% 1.53/0.58  fof(f45,plain,(
% 1.53/0.58    v3_funct_2(sK1,sK0,sK0)),
% 1.53/0.58    inference(cnf_transformation,[],[f40])).
% 1.53/0.58  fof(f83,plain,(
% 1.53/0.58    spl2_2),
% 1.53/0.58    inference(avatar_split_clause,[],[f44,f80])).
% 1.53/0.58  fof(f44,plain,(
% 1.53/0.58    v1_funct_2(sK1,sK0,sK0)),
% 1.53/0.58    inference(cnf_transformation,[],[f40])).
% 1.53/0.58  fof(f78,plain,(
% 1.53/0.58    spl2_1),
% 1.53/0.58    inference(avatar_split_clause,[],[f43,f75])).
% 1.53/0.58  fof(f43,plain,(
% 1.53/0.58    v1_funct_1(sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f40])).
% 1.53/0.58  % SZS output end Proof for theBenchmark
% 1.53/0.58  % (1611)------------------------------
% 1.53/0.58  % (1611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (1611)Termination reason: Refutation
% 1.53/0.58  
% 1.53/0.58  % (1611)Memory used [KB]: 11001
% 1.53/0.58  % (1611)Time elapsed: 0.136 s
% 1.53/0.58  % (1611)------------------------------
% 1.53/0.58  % (1611)------------------------------
% 1.53/0.58  % (1599)Success in time 0.219 s
%------------------------------------------------------------------------------
