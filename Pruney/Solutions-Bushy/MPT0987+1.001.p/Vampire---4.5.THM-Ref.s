%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0987+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:01 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 293 expanded)
%              Number of leaves         :   29 ( 105 expanded)
%              Depth                    :   10
%              Number of atoms          :  434 (1016 expanded)
%              Number of equality atoms :   40 (  62 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f439,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f71,f75,f107,f111,f115,f127,f131,f145,f158,f237,f331,f347,f403,f411,f431,f438])).

fof(f438,plain,
    ( ~ spl5_34
    | ~ spl5_44
    | spl5_46
    | ~ spl5_51 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | ~ spl5_34
    | ~ spl5_44
    | spl5_46
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f436,f410])).

fof(f410,plain,
    ( ~ v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | spl5_46 ),
    inference(avatar_component_clause,[],[f409])).

fof(f409,plain,
    ( spl5_46
  <=> v2_funct_2(k5_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f436,plain,
    ( v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | ~ spl5_34
    | ~ spl5_44
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f435,f330])).

fof(f330,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl5_34
  <=> v1_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f435,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | ~ spl5_44
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f433,f402])).

fof(f402,plain,
    ( v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f401])).

fof(f401,plain,
    ( spl5_44
  <=> v5_relat_1(k5_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f433,plain,
    ( ~ v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | ~ spl5_51 ),
    inference(superposition,[],[f49,f430])).

fof(f430,plain,
    ( sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f429])).

fof(f429,plain,
    ( spl5_51
  <=> sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f49,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f431,plain,
    ( spl5_51
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f391,f156,f129,f125,f113,f105,f429])).

fof(f105,plain,
    ( spl5_7
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f113,plain,
    ( spl5_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f125,plain,
    ( spl5_12
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f129,plain,
    ( spl5_13
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f156,plain,
    ( spl5_18
  <=> r1_tarski(k1_relat_1(sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f391,plain,
    ( sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f390,f126])).

fof(f126,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f390,plain,
    ( k2_relat_1(sK4) = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f389,f106])).

fof(f106,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f389,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(resolution,[],[f137,f157])).

fof(f157,plain,
    ( r1_tarski(k1_relat_1(sK4),sK0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f156])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(X0),sK0)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK3,X0)) )
    | ~ spl5_9
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f135,f114])).

fof(f114,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(X0),sK0)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK3,X0)) )
    | ~ spl5_13 ),
    inference(superposition,[],[f44,f130])).

fof(f130,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f411,plain,
    ( ~ spl5_46
    | spl5_8
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f384,f345,f109,f409])).

fof(f109,plain,
    ( spl5_8
  <=> v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f345,plain,
    ( spl5_38
  <=> k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f384,plain,
    ( ~ v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | spl5_8
    | ~ spl5_38 ),
    inference(superposition,[],[f110,f346])).

fof(f346,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f345])).

fof(f110,plain,
    ( ~ v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f403,plain,
    ( spl5_44
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f280,f235,f401])).

fof(f235,plain,
    ( spl5_30
  <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f280,plain,
    ( v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ spl5_30 ),
    inference(resolution,[],[f236,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f236,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f235])).

fof(f347,plain,
    ( spl5_38
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f194,f73,f69,f55,f51,f345])).

fof(f51,plain,
    ( spl5_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f55,plain,
    ( spl5_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f69,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f73,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f194,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f192,f52])).

fof(f52,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f192,plain,
    ( ~ v1_funct_1(sK4)
    | k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f100,f70])).

fof(f70,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f100,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X6)
        | k1_partfun1(sK1,sK0,X7,X8,sK3,X6) = k5_relat_1(sK3,X6) )
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f92,f56])).

fof(f56,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f92,plain,
    ( ! [X6,X8,X7] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | k1_partfun1(sK1,sK0,X7,X8,sK3,X6) = k5_relat_1(sK3,X6) )
    | ~ spl5_6 ),
    inference(resolution,[],[f74,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f74,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f331,plain,
    ( spl5_34
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f281,f235,f329])).

fof(f281,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_30 ),
    inference(resolution,[],[f236,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f237,plain,
    ( spl5_30
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f214,f73,f69,f55,f51,f235])).

fof(f214,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f213,f194])).

fof(f213,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f211,f52])).

fof(f211,plain,
    ( ~ v1_funct_1(sK4)
    | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f99,f70])).

fof(f99,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | m1_subset_1(k1_partfun1(sK1,sK0,X4,X5,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK1,X5))) )
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f91,f56])).

fof(f91,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | m1_subset_1(k1_partfun1(sK1,sK0,X4,X5,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK1,X5))) )
    | ~ spl5_6 ),
    inference(resolution,[],[f74,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f158,plain,
    ( spl5_18
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f154,f143,f156])).

fof(f143,plain,
    ( spl5_15
  <=> m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f154,plain,
    ( r1_tarski(k1_relat_1(sK4),sK0)
    | ~ spl5_15 ),
    inference(resolution,[],[f144,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f144,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f143])).

fof(f145,plain,
    ( spl5_15
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f89,f69,f143])).

fof(f89,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f82,f79])).

fof(f79,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f70,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f82,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK2,sK4),k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f131,plain,
    ( spl5_13
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f102,f73,f59,f129])).

fof(f59,plain,
    ( spl5_3
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f102,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f101,f95])).

fof(f95,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_6 ),
    inference(resolution,[],[f74,f46])).

fof(f101,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f66,f94])).

fof(f94,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f74,f45])).

fof(f66,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | sK0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl5_3 ),
    inference(resolution,[],[f60,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f127,plain,
    ( spl5_12
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f88,f69,f63,f125])).

fof(f63,plain,
    ( spl5_4
  <=> v2_funct_2(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f88,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f87,f81])).

fof(f81,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f70,f46])).

fof(f87,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f67,f80])).

fof(f80,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f70,f45])).

fof(f67,plain,
    ( ~ v5_relat_1(sK4,sK2)
    | sK2 = k2_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_4 ),
    inference(resolution,[],[f64,f42])).

fof(f64,plain,
    ( v2_funct_2(sK4,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f115,plain,
    ( spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f95,f73,f113])).

fof(f111,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f35,f109])).

fof(f35,plain,(
    ~ v2_funct_2(k1_partfun1(sK1,sK0,sK0,sK2,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X1,X0,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
          & v2_funct_2(X4,X2)
          & v2_funct_2(X3,X1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X1,X0,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
          & v2_funct_2(X4,X2)
          & v2_funct_2(X3,X1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X1,X0,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X4) )
           => ( ( v2_funct_2(X4,X2)
                & v2_funct_2(X3,X1) )
             => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                      & v1_funct_1(X4) )
                   => ( ( v2_funct_2(X4,X2)
                        & v2_funct_2(X3,X1) )
                     => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                      & v1_funct_2(X4,X1,X2)
                      & v1_funct_1(X4) )
                   => ( ( v2_funct_2(X4,X2)
                        & v2_funct_2(X3,X1) )
                     => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_2(X4,X1,X2)
                    & v1_funct_1(X4) )
                 => ( ( v2_funct_2(X4,X2)
                      & v2_funct_2(X3,X1) )
                   => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_funct_2)).

fof(f107,plain,
    ( spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f81,f69,f105])).

fof(f75,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f37,f73])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    v2_funct_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f33,f59])).

fof(f33,plain,(
    v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f36,f55])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f31,f51])).

fof(f31,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
