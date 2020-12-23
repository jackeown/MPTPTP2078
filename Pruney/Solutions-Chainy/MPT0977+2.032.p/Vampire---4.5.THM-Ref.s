%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:20 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 153 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  263 ( 374 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f65,f74,f78,f85,f97,f109,f160,f166,f174,f176,f211,f217,f225,f228])).

fof(f228,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f73,f84,f224,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f224,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl3_16
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f84,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_5
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f73,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f225,plain,
    ( ~ spl3_4
    | ~ spl3_16
    | ~ spl3_8
    | spl3_15 ),
    inference(avatar_split_clause,[],[f220,f208,f106,f222,f71])).

fof(f106,plain,
    ( spl3_8
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f208,plain,
    ( spl3_15
  <=> r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f220,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | spl3_15 ),
    inference(superposition,[],[f210,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f38,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f210,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f208])).

fof(f217,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f37,f206])).

fof(f206,plain,
    ( ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl3_14
  <=> m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f211,plain,
    ( ~ spl3_1
    | ~ spl3_14
    | ~ spl3_15
    | spl3_7 ),
    inference(avatar_split_clause,[],[f186,f94,f208,f204,f53])).

fof(f53,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f94,plain,
    ( spl3_7
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f186,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_7 ),
    inference(superposition,[],[f96,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f96,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f176,plain,
    ( ~ spl3_4
    | ~ spl3_2
    | ~ spl3_8
    | spl3_11 ),
    inference(avatar_split_clause,[],[f175,f171,f106,f62,f71])).

fof(f62,plain,
    ( spl3_2
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f171,plain,
    ( spl3_11
  <=> r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f175,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(superposition,[],[f173,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f173,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f174,plain,
    ( ~ spl3_4
    | ~ spl3_11
    | spl3_10 ),
    inference(avatar_split_clause,[],[f169,f157,f171,f71])).

fof(f157,plain,
    ( spl3_10
  <=> r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f169,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(superposition,[],[f159,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f159,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f166,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f37,f155])).

fof(f155,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_9
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f160,plain,
    ( ~ spl3_9
    | ~ spl3_1
    | ~ spl3_10
    | spl3_6 ),
    inference(avatar_split_clause,[],[f145,f90,f157,f53,f153])).

fof(f90,plain,
    ( spl3_6
  <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f145,plain,
    ( ~ r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_6 ),
    inference(superposition,[],[f92,f35])).

fof(f92,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f109,plain,
    ( spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f98,f53,f106])).

fof(f98,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f51,f55])).

fof(f55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f97,plain,
    ( ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f32,f94,f90])).

fof(f32,plain,
    ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
    | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
      | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)
        | ~ r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        | ~ r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
          & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2)
        & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).

fof(f85,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f79,f53,f82])).

fof(f79,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f40,f55])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f78,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f75])).

fof(f75,plain,
    ( $false
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f42,f69])).

fof(f69,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_3
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f74,plain,
    ( ~ spl3_3
    | spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f57,f53,f71,f67])).

fof(f57,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_1 ),
    inference(resolution,[],[f41,f55])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f65,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f59,f53,f62])).

fof(f59,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f39,f55])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:33:26 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.23/0.48  % (13104)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.49  % (13096)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.49  % (13104)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f229,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(avatar_sat_refutation,[],[f56,f65,f74,f78,f85,f97,f109,f160,f166,f174,f176,f211,f217,f225,f228])).
% 0.23/0.50  fof(f228,plain,(
% 0.23/0.50    ~spl3_4 | ~spl3_5 | spl3_16),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f226])).
% 0.23/0.50  fof(f226,plain,(
% 0.23/0.50    $false | (~spl3_4 | ~spl3_5 | spl3_16)),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f73,f84,f224,f46])).
% 0.23/0.50  fof(f46,plain,(
% 0.23/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f30])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.23/0.50    inference(nnf_transformation,[],[f26])).
% 0.23/0.50  fof(f26,plain,(
% 0.23/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.50    inference(ennf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.23/0.50  fof(f224,plain,(
% 0.23/0.50    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_16),
% 0.23/0.50    inference(avatar_component_clause,[],[f222])).
% 0.23/0.50  fof(f222,plain,(
% 0.23/0.50    spl3_16 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.23/0.50  fof(f84,plain,(
% 0.23/0.50    v5_relat_1(sK2,sK1) | ~spl3_5),
% 0.23/0.50    inference(avatar_component_clause,[],[f82])).
% 0.23/0.50  fof(f82,plain,(
% 0.23/0.50    spl3_5 <=> v5_relat_1(sK2,sK1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.50  fof(f73,plain,(
% 0.23/0.50    v1_relat_1(sK2) | ~spl3_4),
% 0.23/0.50    inference(avatar_component_clause,[],[f71])).
% 0.23/0.50  fof(f71,plain,(
% 0.23/0.50    spl3_4 <=> v1_relat_1(sK2)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.50  fof(f225,plain,(
% 0.23/0.50    ~spl3_4 | ~spl3_16 | ~spl3_8 | spl3_15),
% 0.23/0.50    inference(avatar_split_clause,[],[f220,f208,f106,f222,f71])).
% 0.23/0.50  fof(f106,plain,(
% 0.23/0.50    spl3_8 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.23/0.50  fof(f208,plain,(
% 0.23/0.50    spl3_15 <=> r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.23/0.50  fof(f220,plain,(
% 0.23/0.50    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2) | spl3_15),
% 0.23/0.50    inference(superposition,[],[f210,f48])).
% 0.23/0.50  fof(f48,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.50    inference(definition_unfolding,[],[f44,f38])).
% 0.23/0.50  fof(f38,plain,(
% 0.23/0.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f11])).
% 0.23/0.50  fof(f11,axiom,(
% 0.23/0.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.23/0.50  fof(f44,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f24])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.50    inference(flattening,[],[f23])).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.50    inference(ennf_transformation,[],[f5])).
% 0.23/0.50  fof(f5,axiom,(
% 0.23/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.23/0.50  fof(f210,plain,(
% 0.23/0.50    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) | spl3_15),
% 0.23/0.50    inference(avatar_component_clause,[],[f208])).
% 0.23/0.50  fof(f217,plain,(
% 0.23/0.50    spl3_14),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f212])).
% 0.23/0.50  fof(f212,plain,(
% 0.23/0.50    $false | spl3_14),
% 0.23/0.50    inference(unit_resulting_resolution,[],[f37,f206])).
% 0.23/0.50  fof(f206,plain,(
% 0.23/0.50    ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | spl3_14),
% 0.23/0.50    inference(avatar_component_clause,[],[f204])).
% 0.23/0.50  fof(f204,plain,(
% 0.23/0.50    spl3_14 <=> m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.23/0.50  fof(f37,plain,(
% 0.23/0.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f10])).
% 0.23/0.50  fof(f10,axiom,(
% 0.23/0.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.23/0.50  fof(f211,plain,(
% 0.23/0.50    ~spl3_1 | ~spl3_14 | ~spl3_15 | spl3_7),
% 0.23/0.50    inference(avatar_split_clause,[],[f186,f94,f208,f204,f53])).
% 0.23/0.50  fof(f53,plain,(
% 0.23/0.50    spl3_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.50  fof(f94,plain,(
% 0.23/0.50    spl3_7 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.23/0.50  fof(f186,plain,(
% 0.23/0.50    ~r2_relset_1(sK0,sK1,k5_relat_1(sK2,k6_partfun1(sK1)),sK2) | ~m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_7),
% 0.23/0.50    inference(superposition,[],[f96,f35])).
% 0.23/0.50  fof(f35,plain,(
% 0.23/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(flattening,[],[f17])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.51    inference(ennf_transformation,[],[f8])).
% 0.23/0.51  fof(f8,axiom,(
% 0.23/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.23/0.51  fof(f96,plain,(
% 0.23/0.51    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | spl3_7),
% 0.23/0.51    inference(avatar_component_clause,[],[f94])).
% 0.23/0.51  fof(f176,plain,(
% 0.23/0.51    ~spl3_4 | ~spl3_2 | ~spl3_8 | spl3_11),
% 0.23/0.51    inference(avatar_split_clause,[],[f175,f171,f106,f62,f71])).
% 0.23/0.51  fof(f62,plain,(
% 0.23/0.51    spl3_2 <=> v4_relat_1(sK2,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.51  fof(f171,plain,(
% 0.23/0.51    spl3_11 <=> r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.23/0.51  fof(f175,plain,(
% 0.23/0.51    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_11),
% 0.23/0.51    inference(superposition,[],[f173,f43])).
% 0.23/0.51  fof(f43,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(flattening,[],[f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.23/0.51    inference(ennf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.23/0.51  fof(f173,plain,(
% 0.23/0.51    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | spl3_11),
% 0.23/0.51    inference(avatar_component_clause,[],[f171])).
% 0.23/0.51  fof(f174,plain,(
% 0.23/0.51    ~spl3_4 | ~spl3_11 | spl3_10),
% 0.23/0.51    inference(avatar_split_clause,[],[f169,f157,f171,f71])).
% 0.23/0.51  fof(f157,plain,(
% 0.23/0.51    spl3_10 <=> r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.23/0.51  fof(f169,plain,(
% 0.23/0.51    ~r2_relset_1(sK0,sK1,k7_relat_1(sK2,sK0),sK2) | ~v1_relat_1(sK2) | spl3_10),
% 0.23/0.51    inference(superposition,[],[f159,f49])).
% 0.23/0.51  fof(f49,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(definition_unfolding,[],[f45,f38])).
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f25])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.23/0.51  fof(f159,plain,(
% 0.23/0.51    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) | spl3_10),
% 0.23/0.51    inference(avatar_component_clause,[],[f157])).
% 0.23/0.51  fof(f166,plain,(
% 0.23/0.51    spl3_9),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f161])).
% 0.23/0.51  fof(f161,plain,(
% 0.23/0.51    $false | spl3_9),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f37,f155])).
% 0.23/0.51  fof(f155,plain,(
% 0.23/0.51    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_9),
% 0.23/0.51    inference(avatar_component_clause,[],[f153])).
% 0.23/0.51  fof(f153,plain,(
% 0.23/0.51    spl3_9 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.23/0.51  fof(f160,plain,(
% 0.23/0.51    ~spl3_9 | ~spl3_1 | ~spl3_10 | spl3_6),
% 0.23/0.51    inference(avatar_split_clause,[],[f145,f90,f157,f53,f153])).
% 0.23/0.51  fof(f90,plain,(
% 0.23/0.51    spl3_6 <=> r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.23/0.51  fof(f145,plain,(
% 0.23/0.51    ~r2_relset_1(sK0,sK1,k5_relat_1(k6_partfun1(sK0),sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_6),
% 0.23/0.51    inference(superposition,[],[f92,f35])).
% 0.23/0.51  fof(f92,plain,(
% 0.23/0.51    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2) | spl3_6),
% 0.23/0.51    inference(avatar_component_clause,[],[f90])).
% 0.23/0.51  fof(f109,plain,(
% 0.23/0.51    spl3_8 | ~spl3_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f98,f53,f106])).
% 0.23/0.51  fof(f98,plain,(
% 0.23/0.51    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl3_1),
% 0.23/0.51    inference(resolution,[],[f51,f55])).
% 0.23/0.51  fof(f55,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_1),
% 0.23/0.51    inference(avatar_component_clause,[],[f53])).
% 0.23/0.51  fof(f51,plain,(
% 0.23/0.51    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f50])).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.51    inference(equality_resolution,[],[f34])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f29])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(nnf_transformation,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(flattening,[],[f15])).
% 0.23/0.51  fof(f15,plain,(
% 0.23/0.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.51    inference(ennf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,axiom,(
% 0.23/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.23/0.51  fof(f97,plain,(
% 0.23/0.51    ~spl3_6 | ~spl3_7),
% 0.23/0.51    inference(avatar_split_clause,[],[f32,f94,f90])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)),
% 0.23/0.51    inference(cnf_transformation,[],[f28])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    (~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f27])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK1,sK1,sK1,sK2,k6_partfun1(sK1)),sK2) | ~r2_relset_1(sK0,sK1,k4_relset_1(sK0,sK0,sK0,sK1,k6_partfun1(sK0),sK2),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f14,plain,(
% 0.23/0.51    ? [X0,X1,X2] : ((~r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) | ~r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f13])).
% 0.23/0.51  fof(f13,negated_conjecture,(
% 0.23/0.51    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.23/0.51    inference(negated_conjecture,[],[f12])).
% 0.23/0.51  fof(f12,conjecture,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r2_relset_1(X0,X1,k4_relset_1(X0,X1,X1,X1,X2,k6_partfun1(X1)),X2) & r2_relset_1(X0,X1,k4_relset_1(X0,X0,X0,X1,k6_partfun1(X0),X2),X2)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_2)).
% 0.23/0.51  fof(f85,plain,(
% 0.23/0.51    spl3_5 | ~spl3_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f79,f53,f82])).
% 0.23/0.51  fof(f79,plain,(
% 0.23/0.51    v5_relat_1(sK2,sK1) | ~spl3_1),
% 0.23/0.51    inference(resolution,[],[f40,f55])).
% 0.23/0.51  fof(f40,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.23/0.51  fof(f78,plain,(
% 0.23/0.51    spl3_3),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f75])).
% 0.23/0.51  fof(f75,plain,(
% 0.23/0.51    $false | spl3_3),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f42,f69])).
% 0.23/0.51  fof(f69,plain,(
% 0.23/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_3),
% 0.23/0.51    inference(avatar_component_clause,[],[f67])).
% 0.23/0.51  fof(f67,plain,(
% 0.23/0.51    spl3_3 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.51  fof(f42,plain,(
% 0.23/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.23/0.51  fof(f74,plain,(
% 0.23/0.51    ~spl3_3 | spl3_4 | ~spl3_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f57,f53,f71,f67])).
% 0.23/0.51  fof(f57,plain,(
% 0.23/0.51    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl3_1),
% 0.23/0.51    inference(resolution,[],[f41,f55])).
% 0.23/0.51  fof(f41,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.23/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.23/0.51  fof(f65,plain,(
% 0.23/0.51    spl3_2 | ~spl3_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f59,f53,f62])).
% 0.23/0.51  fof(f59,plain,(
% 0.23/0.51    v4_relat_1(sK2,sK0) | ~spl3_1),
% 0.23/0.51    inference(resolution,[],[f39,f55])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    spl3_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f31,f53])).
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.51    inference(cnf_transformation,[],[f28])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (13104)------------------------------
% 0.23/0.51  % (13104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (13104)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (13104)Memory used [KB]: 10874
% 0.23/0.51  % (13104)Time elapsed: 0.071 s
% 0.23/0.51  % (13104)------------------------------
% 0.23/0.51  % (13104)------------------------------
% 0.23/0.51  % (13080)Success in time 0.14 s
%------------------------------------------------------------------------------
