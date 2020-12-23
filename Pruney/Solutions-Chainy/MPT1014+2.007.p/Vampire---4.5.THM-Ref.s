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
% DateTime   : Thu Dec  3 13:05:24 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 244 expanded)
%              Number of leaves         :   30 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  436 ( 855 expanded)
%              Number of equality atoms :   93 ( 142 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f883,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f68,f76,f80,f84,f88,f105,f129,f137,f145,f157,f162,f256,f335,f396,f421,f881,f882])).

fof(f882,plain,
    ( sK2 != k6_relat_1(sK0)
    | r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f881,plain,
    ( ~ spl3_7
    | ~ spl3_28
    | spl3_32
    | ~ spl3_54 ),
    inference(avatar_contradiction_clause,[],[f880])).

fof(f880,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_28
    | spl3_32
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f879,f83])).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f879,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_28
    | spl3_32
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f878,f331])).

fof(f331,plain,
    ( sK1 != k5_relat_1(sK1,sK2)
    | spl3_32 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl3_32
  <=> sK1 = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f878,plain,
    ( sK1 = k5_relat_1(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_28
    | ~ spl3_54 ),
    inference(resolution,[],[f288,f420])).

fof(f420,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl3_54
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),X0)
        | k5_relat_1(sK1,sK2) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl3_28 ),
    inference(resolution,[],[f255,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f255,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl3_28
  <=> m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f421,plain,
    ( spl3_54
    | ~ spl3_11
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f417,f394,f127,f419])).

fof(f127,plain,
    ( spl3_11
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f394,plain,
    ( spl3_48
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f417,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)
    | ~ spl3_11
    | ~ spl3_48 ),
    inference(superposition,[],[f128,f395])).

fof(f395,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f394])).

fof(f128,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f396,plain,
    ( spl3_48
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f251,f82,f74,f58,f54,f394])).

fof(f54,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f58,plain,
    ( spl3_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f74,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f251,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f248,f55])).

fof(f55,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f248,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f116,f75])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f116,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X1)
        | k5_relat_1(sK1,X1) = k1_partfun1(sK0,sK0,X2,X3,sK1,X1) )
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f108,f59])).

fof(f59,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f108,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k5_relat_1(sK1,X1) = k1_partfun1(sK0,sK0,X2,X3,sK1,X1) )
    | ~ spl3_7 ),
    inference(resolution,[],[f83,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f335,plain,
    ( ~ spl3_32
    | spl3_33
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f194,f159,f103,f82,f78,f58,f54,f333,f330])).

fof(f333,plain,
    ( spl3_33
  <=> sK2 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f78,plain,
    ( spl3_6
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f103,plain,
    ( spl3_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f159,plain,
    ( spl3_19
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f194,plain,
    ( sK2 = k6_relat_1(sK0)
    | sK1 != k5_relat_1(sK1,sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f193,f104])).

fof(f104,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f193,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0)
    | sK1 != k5_relat_1(sK1,sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f191,f160])).

fof(f160,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f159])).

fof(f191,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k6_relat_1(sK0)
    | sK1 != k5_relat_1(sK1,sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f119,f55])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | k6_relat_1(sK0) = X0
        | sK1 != k5_relat_1(sK1,X0) )
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f118,f115])).

fof(f115,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f106,f79])).

fof(f79,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f106,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f118,plain,
    ( ! [X0] :
        ( sK0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | sK1 != k5_relat_1(sK1,X0)
        | k6_relat_1(k2_relat_1(sK1)) = X0 )
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f117,f115])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK1)
        | sK1 != k5_relat_1(sK1,X0)
        | k6_relat_1(k2_relat_1(sK1)) = X0 )
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f64,f111])).

fof(f111,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f83,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f64,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK1)
        | sK1 != k5_relat_1(sK1,X0)
        | k6_relat_1(k2_relat_1(sK1)) = X0 )
    | ~ spl3_2 ),
    inference(inner_rewriting,[],[f63])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK1)
        | sK1 != k5_relat_1(sK1,X0)
        | k6_relat_1(k1_relat_1(X0)) = X0 )
    | ~ spl3_2 ),
    inference(resolution,[],[f59,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k5_relat_1(X0,X1) != X0
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f256,plain,
    ( spl3_28
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f207,f82,f74,f254])).

fof(f207,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f205,f185])).

fof(f185,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f109,f75])).

fof(f109,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k4_relset_1(sK0,sK0,X5,X6,sK1,X4) = k5_relat_1(sK1,X4) )
    | ~ spl3_7 ),
    inference(resolution,[],[f83,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f205,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f112,f75])).

fof(f112,plain,
    ( ! [X8,X7,X9] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | m1_subset_1(k4_relset_1(sK0,sK0,X8,X9,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(sK0,X9))) )
    | ~ spl3_7 ),
    inference(resolution,[],[f83,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f162,plain,
    ( spl3_19
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f161,f155,f143,f159])).

fof(f143,plain,
    ( spl3_15
  <=> sK0 = k1_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f155,plain,
    ( spl3_18
  <=> k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f161,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_15
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f156,f144])).

fof(f144,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f143])).

fof(f156,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( spl3_18
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f93,f74,f155])).

fof(f93,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f145,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f101,f74,f66,f54,f143])).

fof(f66,plain,
    ( spl3_3
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f101,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f100,f55])).

fof(f100,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f97,f67])).

fof(f67,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f97,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f75,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

% (396)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f21,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f137,plain,
    ( spl3_13
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f96,f74,f135])).

fof(f135,plain,
    ( spl3_13
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f96,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f129,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f33,f127])).

fof(f33,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( k2_relset_1(X0,X0,X1) = X0
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_funct_2)).

fof(f105,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f94,f74,f103])).

fof(f94,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f75,f48])).

fof(f88,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f52,f86])).

fof(f86,plain,
    ( spl3_8
  <=> r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f52,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f35,f39])).

fof(f39,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f35,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f84,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f32,f74])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f36,f58])).

fof(f36,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:41:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (413)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.47  % (421)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (400)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (399)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (424)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (424)Refutation not found, incomplete strategy% (424)------------------------------
% 0.22/0.52  % (424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (424)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (424)Memory used [KB]: 1663
% 0.22/0.52  % (424)Time elapsed: 0.001 s
% 0.22/0.52  % (424)------------------------------
% 0.22/0.52  % (424)------------------------------
% 1.24/0.52  % (394)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.53  % (395)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.53  % (417)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.24/0.53  % (421)Refutation found. Thanks to Tanya!
% 1.24/0.53  % SZS status Theorem for theBenchmark
% 1.24/0.53  % SZS output start Proof for theBenchmark
% 1.24/0.53  fof(f883,plain,(
% 1.24/0.53    $false),
% 1.24/0.53    inference(avatar_sat_refutation,[],[f56,f60,f68,f76,f80,f84,f88,f105,f129,f137,f145,f157,f162,f256,f335,f396,f421,f881,f882])).
% 1.24/0.53  fof(f882,plain,(
% 1.24/0.53    sK2 != k6_relat_1(sK0) | r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.24/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.24/0.53  fof(f881,plain,(
% 1.24/0.53    ~spl3_7 | ~spl3_28 | spl3_32 | ~spl3_54),
% 1.24/0.53    inference(avatar_contradiction_clause,[],[f880])).
% 1.24/0.53  fof(f880,plain,(
% 1.24/0.53    $false | (~spl3_7 | ~spl3_28 | spl3_32 | ~spl3_54)),
% 1.24/0.53    inference(subsumption_resolution,[],[f879,f83])).
% 1.24/0.53  fof(f83,plain,(
% 1.24/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_7),
% 1.24/0.53    inference(avatar_component_clause,[],[f82])).
% 1.24/0.53  fof(f82,plain,(
% 1.24/0.53    spl3_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.24/0.53  fof(f879,plain,(
% 1.24/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_28 | spl3_32 | ~spl3_54)),
% 1.24/0.53    inference(subsumption_resolution,[],[f878,f331])).
% 1.24/0.53  fof(f331,plain,(
% 1.24/0.53    sK1 != k5_relat_1(sK1,sK2) | spl3_32),
% 1.24/0.53    inference(avatar_component_clause,[],[f330])).
% 1.24/0.53  fof(f330,plain,(
% 1.24/0.53    spl3_32 <=> sK1 = k5_relat_1(sK1,sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.24/0.53  fof(f878,plain,(
% 1.24/0.53    sK1 = k5_relat_1(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_28 | ~spl3_54)),
% 1.24/0.53    inference(resolution,[],[f288,f420])).
% 1.24/0.53  fof(f420,plain,(
% 1.24/0.53    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) | ~spl3_54),
% 1.24/0.53    inference(avatar_component_clause,[],[f419])).
% 1.24/0.53  fof(f419,plain,(
% 1.24/0.53    spl3_54 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 1.24/0.53  fof(f288,plain,(
% 1.24/0.53    ( ! [X0] : (~r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),X0) | k5_relat_1(sK1,sK2) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ) | ~spl3_28),
% 1.24/0.53    inference(resolution,[],[f255,f42])).
% 1.24/0.53  fof(f42,plain,(
% 1.24/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f17])).
% 1.24/0.53  fof(f17,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(flattening,[],[f16])).
% 1.24/0.53  fof(f16,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.24/0.53    inference(ennf_transformation,[],[f7])).
% 1.24/0.53  fof(f7,axiom,(
% 1.24/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.24/0.53  fof(f255,plain,(
% 1.24/0.53    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_28),
% 1.24/0.53    inference(avatar_component_clause,[],[f254])).
% 1.24/0.53  fof(f254,plain,(
% 1.24/0.53    spl3_28 <=> m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.24/0.53  fof(f421,plain,(
% 1.24/0.53    spl3_54 | ~spl3_11 | ~spl3_48),
% 1.24/0.53    inference(avatar_split_clause,[],[f417,f394,f127,f419])).
% 1.24/0.53  fof(f127,plain,(
% 1.24/0.53    spl3_11 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.24/0.53  fof(f394,plain,(
% 1.24/0.53    spl3_48 <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 1.24/0.53  fof(f417,plain,(
% 1.24/0.53    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) | (~spl3_11 | ~spl3_48)),
% 1.24/0.53    inference(superposition,[],[f128,f395])).
% 1.24/0.53  fof(f395,plain,(
% 1.24/0.53    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) | ~spl3_48),
% 1.24/0.53    inference(avatar_component_clause,[],[f394])).
% 1.24/0.53  fof(f128,plain,(
% 1.24/0.53    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1) | ~spl3_11),
% 1.24/0.53    inference(avatar_component_clause,[],[f127])).
% 1.24/0.53  fof(f396,plain,(
% 1.24/0.53    spl3_48 | ~spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_7),
% 1.24/0.53    inference(avatar_split_clause,[],[f251,f82,f74,f58,f54,f394])).
% 1.24/0.53  fof(f54,plain,(
% 1.24/0.53    spl3_1 <=> v1_funct_1(sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.24/0.53  fof(f58,plain,(
% 1.24/0.53    spl3_2 <=> v1_funct_1(sK1)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.24/0.53  fof(f74,plain,(
% 1.24/0.53    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.24/0.53  fof(f251,plain,(
% 1.24/0.53    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) | (~spl3_1 | ~spl3_2 | ~spl3_5 | ~spl3_7)),
% 1.24/0.53    inference(subsumption_resolution,[],[f248,f55])).
% 1.24/0.53  fof(f55,plain,(
% 1.24/0.53    v1_funct_1(sK2) | ~spl3_1),
% 1.24/0.53    inference(avatar_component_clause,[],[f54])).
% 1.24/0.53  fof(f248,plain,(
% 1.24/0.53    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) | (~spl3_2 | ~spl3_5 | ~spl3_7)),
% 1.24/0.53    inference(resolution,[],[f116,f75])).
% 1.24/0.53  fof(f75,plain,(
% 1.24/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_5),
% 1.24/0.53    inference(avatar_component_clause,[],[f74])).
% 1.24/0.53  fof(f116,plain,(
% 1.24/0.53    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X1) | k5_relat_1(sK1,X1) = k1_partfun1(sK0,sK0,X2,X3,sK1,X1)) ) | (~spl3_2 | ~spl3_7)),
% 1.24/0.53    inference(subsumption_resolution,[],[f108,f59])).
% 1.24/0.53  fof(f59,plain,(
% 1.24/0.53    v1_funct_1(sK1) | ~spl3_2),
% 1.24/0.53    inference(avatar_component_clause,[],[f58])).
% 1.24/0.53  fof(f108,plain,(
% 1.24/0.53    ( ! [X2,X3,X1] : (~v1_funct_1(sK1) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k5_relat_1(sK1,X1) = k1_partfun1(sK0,sK0,X2,X3,sK1,X1)) ) | ~spl3_7),
% 1.24/0.53    inference(resolution,[],[f83,f43])).
% 1.24/0.53  fof(f43,plain,(
% 1.24/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f19])).
% 1.24/0.53  fof(f19,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.24/0.53    inference(flattening,[],[f18])).
% 1.24/0.53  fof(f18,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.24/0.53    inference(ennf_transformation,[],[f8])).
% 1.24/0.53  fof(f8,axiom,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.24/0.53  fof(f335,plain,(
% 1.24/0.53    ~spl3_32 | spl3_33 | ~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_19),
% 1.24/0.53    inference(avatar_split_clause,[],[f194,f159,f103,f82,f78,f58,f54,f333,f330])).
% 1.24/0.53  fof(f333,plain,(
% 1.24/0.53    spl3_33 <=> sK2 = k6_relat_1(sK0)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.24/0.53  fof(f78,plain,(
% 1.24/0.53    spl3_6 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.24/0.53  fof(f103,plain,(
% 1.24/0.53    spl3_9 <=> v1_relat_1(sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.24/0.53  fof(f159,plain,(
% 1.24/0.53    spl3_19 <=> sK0 = k1_relat_1(sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.24/0.53  fof(f194,plain,(
% 1.24/0.53    sK2 = k6_relat_1(sK0) | sK1 != k5_relat_1(sK1,sK2) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_19)),
% 1.24/0.53    inference(subsumption_resolution,[],[f193,f104])).
% 1.24/0.53  fof(f104,plain,(
% 1.24/0.53    v1_relat_1(sK2) | ~spl3_9),
% 1.24/0.53    inference(avatar_component_clause,[],[f103])).
% 1.24/0.53  fof(f193,plain,(
% 1.24/0.53    ~v1_relat_1(sK2) | sK2 = k6_relat_1(sK0) | sK1 != k5_relat_1(sK1,sK2) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7 | ~spl3_19)),
% 1.24/0.53    inference(subsumption_resolution,[],[f191,f160])).
% 1.24/0.53  fof(f160,plain,(
% 1.24/0.53    sK0 = k1_relat_1(sK2) | ~spl3_19),
% 1.24/0.53    inference(avatar_component_clause,[],[f159])).
% 1.24/0.53  fof(f191,plain,(
% 1.24/0.53    sK0 != k1_relat_1(sK2) | ~v1_relat_1(sK2) | sK2 = k6_relat_1(sK0) | sK1 != k5_relat_1(sK1,sK2) | (~spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7)),
% 1.24/0.53    inference(resolution,[],[f119,f55])).
% 1.24/0.53  fof(f119,plain,(
% 1.24/0.53    ( ! [X0] : (~v1_funct_1(X0) | sK0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k6_relat_1(sK0) = X0 | sK1 != k5_relat_1(sK1,X0)) ) | (~spl3_2 | ~spl3_6 | ~spl3_7)),
% 1.24/0.53    inference(forward_demodulation,[],[f118,f115])).
% 1.24/0.53  fof(f115,plain,(
% 1.24/0.53    sK0 = k2_relat_1(sK1) | (~spl3_6 | ~spl3_7)),
% 1.24/0.53    inference(forward_demodulation,[],[f106,f79])).
% 1.24/0.53  fof(f79,plain,(
% 1.24/0.53    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl3_6),
% 1.24/0.53    inference(avatar_component_clause,[],[f78])).
% 1.24/0.53  fof(f106,plain,(
% 1.24/0.53    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) | ~spl3_7),
% 1.24/0.53    inference(resolution,[],[f83,f40])).
% 1.24/0.53  fof(f40,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f15])).
% 1.24/0.53  fof(f15,plain,(
% 1.24/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(ennf_transformation,[],[f5])).
% 1.24/0.53  fof(f5,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.24/0.53  fof(f118,plain,(
% 1.24/0.53    ( ! [X0] : (sK0 != k1_relat_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | sK1 != k5_relat_1(sK1,X0) | k6_relat_1(k2_relat_1(sK1)) = X0) ) | (~spl3_2 | ~spl3_6 | ~spl3_7)),
% 1.24/0.53    inference(forward_demodulation,[],[f117,f115])).
% 1.24/0.53  fof(f117,plain,(
% 1.24/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK1) | sK1 != k5_relat_1(sK1,X0) | k6_relat_1(k2_relat_1(sK1)) = X0) ) | (~spl3_2 | ~spl3_7)),
% 1.24/0.53    inference(subsumption_resolution,[],[f64,f111])).
% 1.24/0.53  fof(f111,plain,(
% 1.24/0.53    v1_relat_1(sK1) | ~spl3_7),
% 1.24/0.53    inference(resolution,[],[f83,f48])).
% 1.24/0.53  fof(f48,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f27])).
% 1.24/0.53  fof(f27,plain,(
% 1.24/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(ennf_transformation,[],[f2])).
% 1.24/0.53  fof(f2,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.24/0.53  fof(f64,plain,(
% 1.24/0.53    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK1) | sK1 != k5_relat_1(sK1,X0) | k6_relat_1(k2_relat_1(sK1)) = X0) ) | ~spl3_2),
% 1.24/0.53    inference(inner_rewriting,[],[f63])).
% 1.24/0.53  fof(f63,plain,(
% 1.24/0.53    ( ! [X0] : (~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK1) | sK1 != k5_relat_1(sK1,X0) | k6_relat_1(k1_relat_1(X0)) = X0) ) | ~spl3_2),
% 1.24/0.53    inference(resolution,[],[f59,f45])).
% 1.24/0.53  fof(f45,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X0) != k1_relat_1(X1) | k5_relat_1(X0,X1) != X0 | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 1.24/0.53    inference(cnf_transformation,[],[f23])).
% 1.24/0.53  fof(f23,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.24/0.53    inference(flattening,[],[f22])).
% 1.24/0.53  fof(f22,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.24/0.53    inference(ennf_transformation,[],[f1])).
% 1.24/0.53  fof(f1,axiom,(
% 1.24/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).
% 1.24/0.53  fof(f256,plain,(
% 1.24/0.53    spl3_28 | ~spl3_5 | ~spl3_7),
% 1.24/0.53    inference(avatar_split_clause,[],[f207,f82,f74,f254])).
% 1.24/0.53  fof(f207,plain,(
% 1.24/0.53    m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_5 | ~spl3_7)),
% 1.24/0.53    inference(forward_demodulation,[],[f205,f185])).
% 1.24/0.53  fof(f185,plain,(
% 1.24/0.53    k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) | (~spl3_5 | ~spl3_7)),
% 1.24/0.53    inference(resolution,[],[f109,f75])).
% 1.24/0.53  fof(f109,plain,(
% 1.24/0.53    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k4_relset_1(sK0,sK0,X5,X6,sK1,X4) = k5_relat_1(sK1,X4)) ) | ~spl3_7),
% 1.24/0.53    inference(resolution,[],[f83,f46])).
% 1.24/0.53  fof(f46,plain,(
% 1.24/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f25])).
% 1.24/0.53  fof(f25,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(flattening,[],[f24])).
% 1.24/0.53  fof(f24,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.24/0.53    inference(ennf_transformation,[],[f6])).
% 1.24/0.53  fof(f6,axiom,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 1.24/0.53  fof(f205,plain,(
% 1.24/0.53    m1_subset_1(k4_relset_1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_5 | ~spl3_7)),
% 1.24/0.53    inference(resolution,[],[f112,f75])).
% 1.24/0.53  fof(f112,plain,(
% 1.24/0.53    ( ! [X8,X7,X9] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | m1_subset_1(k4_relset_1(sK0,sK0,X8,X9,sK1,X7),k1_zfmisc_1(k2_zfmisc_1(sK0,X9)))) ) | ~spl3_7),
% 1.24/0.53    inference(resolution,[],[f83,f49])).
% 1.24/0.53  fof(f49,plain,(
% 1.24/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f29])).
% 1.24/0.53  fof(f29,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(flattening,[],[f28])).
% 1.24/0.53  fof(f28,plain,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.24/0.53    inference(ennf_transformation,[],[f3])).
% 1.24/0.53  fof(f3,axiom,(
% 1.24/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 1.24/0.53  fof(f162,plain,(
% 1.24/0.53    spl3_19 | ~spl3_15 | ~spl3_18),
% 1.24/0.53    inference(avatar_split_clause,[],[f161,f155,f143,f159])).
% 1.24/0.53  fof(f143,plain,(
% 1.24/0.53    spl3_15 <=> sK0 = k1_relset_1(sK0,sK0,sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.24/0.53  fof(f155,plain,(
% 1.24/0.53    spl3_18 <=> k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.24/0.53  fof(f161,plain,(
% 1.24/0.53    sK0 = k1_relat_1(sK2) | (~spl3_15 | ~spl3_18)),
% 1.24/0.53    inference(forward_demodulation,[],[f156,f144])).
% 1.24/0.53  fof(f144,plain,(
% 1.24/0.53    sK0 = k1_relset_1(sK0,sK0,sK2) | ~spl3_15),
% 1.24/0.53    inference(avatar_component_clause,[],[f143])).
% 1.24/0.53  fof(f156,plain,(
% 1.24/0.53    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) | ~spl3_18),
% 1.24/0.53    inference(avatar_component_clause,[],[f155])).
% 1.24/0.53  fof(f157,plain,(
% 1.24/0.53    spl3_18 | ~spl3_5),
% 1.24/0.53    inference(avatar_split_clause,[],[f93,f74,f155])).
% 1.24/0.53  fof(f93,plain,(
% 1.24/0.53    k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) | ~spl3_5),
% 1.24/0.53    inference(resolution,[],[f75,f47])).
% 1.24/0.53  fof(f47,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f26])).
% 1.24/0.53  fof(f26,plain,(
% 1.24/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.24/0.53    inference(ennf_transformation,[],[f4])).
% 1.24/0.53  fof(f4,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.24/0.53  fof(f145,plain,(
% 1.24/0.53    spl3_15 | ~spl3_1 | ~spl3_3 | ~spl3_5),
% 1.24/0.53    inference(avatar_split_clause,[],[f101,f74,f66,f54,f143])).
% 1.24/0.53  fof(f66,plain,(
% 1.24/0.53    spl3_3 <=> v1_funct_2(sK2,sK0,sK0)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.24/0.53  fof(f101,plain,(
% 1.24/0.53    sK0 = k1_relset_1(sK0,sK0,sK2) | (~spl3_1 | ~spl3_3 | ~spl3_5)),
% 1.24/0.53    inference(subsumption_resolution,[],[f100,f55])).
% 1.24/0.53  fof(f100,plain,(
% 1.24/0.53    ~v1_funct_1(sK2) | sK0 = k1_relset_1(sK0,sK0,sK2) | (~spl3_3 | ~spl3_5)),
% 1.24/0.53    inference(subsumption_resolution,[],[f97,f67])).
% 1.24/0.53  fof(f67,plain,(
% 1.24/0.53    v1_funct_2(sK2,sK0,sK0) | ~spl3_3),
% 1.24/0.53    inference(avatar_component_clause,[],[f66])).
% 1.24/0.53  fof(f97,plain,(
% 1.24/0.53    ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | sK0 = k1_relset_1(sK0,sK0,sK2) | ~spl3_5),
% 1.24/0.53    inference(resolution,[],[f75,f44])).
% 1.24/0.53  fof(f44,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k1_relset_1(X0,X0,X1) = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f21])).
% 1.24/0.53  % (396)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.24/0.53  fof(f21,plain,(
% 1.24/0.53    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.24/0.53    inference(flattening,[],[f20])).
% 1.24/0.53  fof(f20,plain,(
% 1.24/0.53    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.24/0.53    inference(ennf_transformation,[],[f10])).
% 1.24/0.53  fof(f10,axiom,(
% 1.24/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 1.24/0.53  fof(f137,plain,(
% 1.24/0.53    spl3_13 | ~spl3_5),
% 1.24/0.53    inference(avatar_split_clause,[],[f96,f74,f135])).
% 1.24/0.53  fof(f135,plain,(
% 1.24/0.53    spl3_13 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.24/0.53  fof(f96,plain,(
% 1.24/0.53    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_5),
% 1.24/0.53    inference(resolution,[],[f75,f51])).
% 1.24/0.53  fof(f51,plain,(
% 1.24/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.24/0.53    inference(duplicate_literal_removal,[],[f50])).
% 1.24/0.53  fof(f50,plain,(
% 1.24/0.53    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.24/0.53    inference(equality_resolution,[],[f41])).
% 1.24/0.53  fof(f41,plain,(
% 1.24/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f17])).
% 1.24/0.53  fof(f129,plain,(
% 1.24/0.53    spl3_11),
% 1.24/0.53    inference(avatar_split_clause,[],[f33,f127])).
% 1.24/0.53  fof(f33,plain,(
% 1.24/0.53    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),sK1)),
% 1.24/0.53    inference(cnf_transformation,[],[f14])).
% 1.24/0.53  fof(f14,plain,(
% 1.24/0.53    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.24/0.53    inference(flattening,[],[f13])).
% 1.24/0.53  fof(f13,plain,(
% 1.24/0.53    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.24/0.53    inference(ennf_transformation,[],[f12])).
% 1.24/0.53  fof(f12,negated_conjecture,(
% 1.24/0.53    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.24/0.53    inference(negated_conjecture,[],[f11])).
% 1.24/0.53  fof(f11,conjecture,(
% 1.24/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_funct_2)).
% 1.24/0.53  fof(f105,plain,(
% 1.24/0.53    spl3_9 | ~spl3_5),
% 1.24/0.53    inference(avatar_split_clause,[],[f94,f74,f103])).
% 1.24/0.53  fof(f94,plain,(
% 1.24/0.53    v1_relat_1(sK2) | ~spl3_5),
% 1.24/0.53    inference(resolution,[],[f75,f48])).
% 1.24/0.53  fof(f88,plain,(
% 1.24/0.53    ~spl3_8),
% 1.24/0.53    inference(avatar_split_clause,[],[f52,f86])).
% 1.24/0.53  fof(f86,plain,(
% 1.24/0.53    spl3_8 <=> r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))),
% 1.24/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.24/0.53  fof(f52,plain,(
% 1.24/0.53    ~r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))),
% 1.24/0.53    inference(forward_demodulation,[],[f35,f39])).
% 1.24/0.53  fof(f39,plain,(
% 1.24/0.53    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f9])).
% 1.24/0.53  fof(f9,axiom,(
% 1.24/0.53    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.24/0.53  fof(f35,plain,(
% 1.24/0.53    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 1.24/0.53    inference(cnf_transformation,[],[f14])).
% 1.24/0.53  fof(f84,plain,(
% 1.24/0.53    spl3_7),
% 1.24/0.53    inference(avatar_split_clause,[],[f38,f82])).
% 1.24/0.53  fof(f38,plain,(
% 1.24/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.24/0.53    inference(cnf_transformation,[],[f14])).
% 1.24/0.53  fof(f80,plain,(
% 1.24/0.53    spl3_6),
% 1.24/0.53    inference(avatar_split_clause,[],[f34,f78])).
% 1.24/0.53  fof(f34,plain,(
% 1.24/0.53    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 1.24/0.53    inference(cnf_transformation,[],[f14])).
% 1.24/0.53  fof(f76,plain,(
% 1.24/0.53    spl3_5),
% 1.24/0.53    inference(avatar_split_clause,[],[f32,f74])).
% 1.24/0.53  fof(f32,plain,(
% 1.24/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.24/0.53    inference(cnf_transformation,[],[f14])).
% 1.24/0.53  fof(f68,plain,(
% 1.24/0.53    spl3_3),
% 1.24/0.53    inference(avatar_split_clause,[],[f31,f66])).
% 1.24/0.53  fof(f31,plain,(
% 1.24/0.53    v1_funct_2(sK2,sK0,sK0)),
% 1.24/0.53    inference(cnf_transformation,[],[f14])).
% 1.24/0.53  fof(f60,plain,(
% 1.24/0.53    spl3_2),
% 1.24/0.53    inference(avatar_split_clause,[],[f36,f58])).
% 1.24/0.53  fof(f36,plain,(
% 1.24/0.53    v1_funct_1(sK1)),
% 1.24/0.53    inference(cnf_transformation,[],[f14])).
% 1.24/0.53  fof(f56,plain,(
% 1.24/0.53    spl3_1),
% 1.24/0.53    inference(avatar_split_clause,[],[f30,f54])).
% 1.24/0.53  fof(f30,plain,(
% 1.24/0.53    v1_funct_1(sK2)),
% 1.24/0.53    inference(cnf_transformation,[],[f14])).
% 1.24/0.53  % SZS output end Proof for theBenchmark
% 1.24/0.53  % (421)------------------------------
% 1.24/0.53  % (421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (421)Termination reason: Refutation
% 1.24/0.53  
% 1.24/0.53  % (421)Memory used [KB]: 7036
% 1.24/0.53  % (421)Time elapsed: 0.123 s
% 1.24/0.53  % (421)------------------------------
% 1.24/0.53  % (421)------------------------------
% 1.24/0.53  % (393)Success in time 0.169 s
%------------------------------------------------------------------------------
