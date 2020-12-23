%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 224 expanded)
%              Number of leaves         :   29 (  96 expanded)
%              Depth                    :    9
%              Number of atoms          :  370 ( 979 expanded)
%              Number of equality atoms :   99 ( 366 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f53,f57,f61,f65,f69,f73,f85,f104,f107,f123,f136,f152,f163,f177,f189,f211,f292,f366,f371])).

fof(f371,plain,
    ( ~ spl5_5
    | ~ spl5_14
    | ~ spl5_17
    | spl5_62 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_17
    | spl5_62 ),
    inference(subsumption_resolution,[],[f60,f369])).

fof(f369,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl5_14
    | ~ spl5_17
    | spl5_62 ),
    inference(trivial_inequality_removal,[],[f368])).

fof(f368,plain,
    ( ! [X0,X1] :
        ( sK2 != sK2
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_14
    | ~ spl5_17
    | spl5_62 ),
    inference(forward_demodulation,[],[f367,f134])).

fof(f134,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_17
  <=> sK2 = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f367,plain,
    ( ! [X0,X1] :
        ( sK2 != k9_relat_1(sK4,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_14
    | spl5_62 ),
    inference(superposition,[],[f365,f113])).

fof(f113,plain,
    ( ! [X2,X0,X1] :
        ( k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl5_14 ),
    inference(resolution,[],[f103,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f103,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,sK1) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_14
  <=> ! [X0] :
        ( k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,sK1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f365,plain,
    ( sK2 != k2_relat_1(k5_relat_1(sK3,sK4))
    | spl5_62 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl5_62
  <=> sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f60,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f59])).

% (4148)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f59,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f366,plain,
    ( ~ spl5_62
    | spl5_26
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f362,f290,f187,f364])).

fof(f187,plain,
    ( spl5_26
  <=> sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f290,plain,
    ( spl5_45
  <=> k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f362,plain,
    ( sK2 != k2_relat_1(k5_relat_1(sK3,sK4))
    | spl5_26
    | ~ spl5_45 ),
    inference(superposition,[],[f188,f291])).

fof(f291,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f290])).

fof(f188,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f187])).

fof(f292,plain,
    ( spl5_45
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f277,f209,f290])).

% (4158)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f209,plain,
    ( spl5_30
  <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f277,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_30 ),
    inference(resolution,[],[f210,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f210,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f209])).

fof(f211,plain,
    ( ~ spl5_8
    | spl5_30
    | ~ spl5_7
    | ~ spl5_21
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f207,f175,f161,f67,f209,f71])).

fof(f71,plain,
    ( spl5_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f67,plain,
    ( spl5_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f161,plain,
    ( spl5_21
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f175,plain,
    ( spl5_24
  <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f207,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | ~ spl5_7
    | ~ spl5_21
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f201,f176])).

fof(f176,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f175])).

fof(f201,plain,
    ( ~ v1_funct_1(sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(resolution,[],[f162,f68])).

fof(f68,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f161])).

fof(f189,plain,
    ( ~ spl5_26
    | spl5_1
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f184,f175,f43,f187])).

fof(f43,plain,
    ( spl5_1
  <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f184,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | spl5_1
    | ~ spl5_24 ),
    inference(superposition,[],[f44,f176])).

fof(f44,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f177,plain,
    ( spl5_24
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f169,f150,f67,f71,f175])).

fof(f150,plain,
    ( spl5_19
  <=> ! [X1,X0,X2] :
        ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f169,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_7
    | ~ spl5_19 ),
    inference(resolution,[],[f151,f68])).

fof(f151,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f150])).

fof(f163,plain,
    ( ~ spl5_6
    | spl5_21
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f158,f59,f161,f63])).

fof(f63,plain,
    ( spl5_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f41,f60])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
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

fof(f152,plain,
    ( ~ spl5_6
    | spl5_19
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f146,f59,f150,f63])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f39,f60])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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

fof(f136,plain,
    ( ~ spl5_5
    | spl5_17
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f130,f121,f133,f59])).

fof(f121,plain,
    ( spl5_15
  <=> sK2 = k7_relset_1(sK1,sK2,sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f130,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_15 ),
    inference(superposition,[],[f38,f122])).

fof(f122,plain,
    ( sK2 = k7_relset_1(sK1,sK2,sK4,sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f121])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f123,plain,
    ( spl5_15
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f119,f59,f51,f121])).

fof(f51,plain,
    ( spl5_3
  <=> sK2 = k2_relset_1(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f119,plain,
    ( sK2 = k7_relset_1(sK1,sK2,sK4,sK1)
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f117,f52])).

fof(f52,plain,
    ( sK2 = k2_relset_1(sK1,sK2,sK4)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f117,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k7_relset_1(sK1,sK2,sK4,sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f36,f60])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f107,plain,
    ( ~ spl5_7
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl5_7
    | spl5_13 ),
    inference(subsumption_resolution,[],[f68,f105])).

fof(f105,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_13 ),
    inference(resolution,[],[f100,f34])).

fof(f100,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f104,plain,
    ( ~ spl5_13
    | spl5_14
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f97,f83,f102,f99])).

fof(f83,plain,
    ( spl5_10
  <=> sK1 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f97,plain,
    ( ! [X0] :
        ( k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_10 ),
    inference(superposition,[],[f33,f84])).

fof(f84,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f85,plain,
    ( spl5_10
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f81,f67,f55,f83])).

fof(f55,plain,
    ( spl5_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f81,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f75,f56])).

fof(f56,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f75,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl5_7 ),
    inference(resolution,[],[f35,f68])).

fof(f73,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f25,f71])).

fof(f25,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & k1_xboole_0 != sK2
    & sK2 = k2_relset_1(sK1,sK2,sK4)
    & sK1 = k2_relset_1(sK0,sK1,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
            & k1_xboole_0 != X2
            & k2_relset_1(X1,X2,X4) = X2
            & k2_relset_1(X0,X1,X3) = X1
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & k1_xboole_0 != sK2
          & sK2 = k2_relset_1(sK1,sK2,X4)
          & sK1 = k2_relset_1(sK0,sK1,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X4] :
        ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
        & k1_xboole_0 != sK2
        & sK2 = k2_relset_1(sK1,sK2,X4)
        & sK1 = k2_relset_1(sK0,sK1,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_1(X4) )
   => ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
      & k1_xboole_0 != sK2
      & sK2 = k2_relset_1(sK1,sK2,sK4)
      & sK1 = k2_relset_1(sK0,sK1,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X1,X2,X4) = X2
                & k2_relset_1(X0,X1,X3) = X1 )
             => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

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

fof(f69,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f28,f59])).

% (4167)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f28,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f30,f51])).

fof(f30,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f32,f43])).

fof(f32,plain,(
    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:53:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (4162)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (4161)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (4154)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (4153)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (4154)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (4164)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (4150)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (4156)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f45,f53,f57,f61,f65,f69,f73,f85,f104,f107,f123,f136,f152,f163,f177,f189,f211,f292,f366,f371])).
% 0.21/0.51  fof(f371,plain,(
% 0.21/0.51    ~spl5_5 | ~spl5_14 | ~spl5_17 | spl5_62),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f370])).
% 0.21/0.51  fof(f370,plain,(
% 0.21/0.51    $false | (~spl5_5 | ~spl5_14 | ~spl5_17 | spl5_62)),
% 0.21/0.51    inference(subsumption_resolution,[],[f60,f369])).
% 0.21/0.51  fof(f369,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_14 | ~spl5_17 | spl5_62)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f368])).
% 0.21/0.51  fof(f368,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sK2 != sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_14 | ~spl5_17 | spl5_62)),
% 0.21/0.51    inference(forward_demodulation,[],[f367,f134])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    sK2 = k9_relat_1(sK4,sK1) | ~spl5_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f133])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    spl5_17 <=> sK2 = k9_relat_1(sK4,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.51  fof(f367,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sK2 != k9_relat_1(sK4,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_14 | spl5_62)),
% 0.21/0.51    inference(superposition,[],[f365,f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl5_14),
% 0.21/0.51    inference(resolution,[],[f103,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,sK1)) ) | ~spl5_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl5_14 <=> ! [X0] : (k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,sK1) | ~v1_relat_1(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.51  fof(f365,plain,(
% 0.21/0.51    sK2 != k2_relat_1(k5_relat_1(sK3,sK4)) | spl5_62),
% 0.21/0.51    inference(avatar_component_clause,[],[f364])).
% 0.21/0.51  fof(f364,plain,(
% 0.21/0.51    spl5_62 <=> sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  % (4148)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl5_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.51  fof(f366,plain,(
% 0.21/0.51    ~spl5_62 | spl5_26 | ~spl5_45),
% 0.21/0.51    inference(avatar_split_clause,[],[f362,f290,f187,f364])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    spl5_26 <=> sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    spl5_45 <=> k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.21/0.51  fof(f362,plain,(
% 0.21/0.51    sK2 != k2_relat_1(k5_relat_1(sK3,sK4)) | (spl5_26 | ~spl5_45)),
% 0.21/0.51    inference(superposition,[],[f188,f291])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) | ~spl5_45),
% 0.21/0.51    inference(avatar_component_clause,[],[f290])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | spl5_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f187])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    spl5_45 | ~spl5_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f277,f209,f290])).
% 0.21/0.51  % (4158)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    spl5_30 <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) | ~spl5_30),
% 0.21/0.51    inference(resolution,[],[f210,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f209])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ~spl5_8 | spl5_30 | ~spl5_7 | ~spl5_21 | ~spl5_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f207,f175,f161,f67,f209,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl5_8 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl5_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl5_21 <=> ! [X1,X0,X2] : (m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    spl5_24 <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK3) | (~spl5_7 | ~spl5_21 | ~spl5_24)),
% 0.21/0.51    inference(forward_demodulation,[],[f201,f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | ~spl5_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f175])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    ~v1_funct_1(sK3) | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_7 | ~spl5_21)),
% 0.21/0.51    inference(resolution,[],[f162,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f67])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | ~spl5_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f161])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    ~spl5_26 | spl5_1 | ~spl5_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f184,f175,f43,f187])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    spl5_1 <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    sK2 != k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | (spl5_1 | ~spl5_24)),
% 0.21/0.51    inference(superposition,[],[f44,f176])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) | spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f43])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    spl5_24 | ~spl5_8 | ~spl5_7 | ~spl5_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f169,f150,f67,f71,f175])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    spl5_19 <=> ! [X1,X0,X2] : (k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl5_7 | ~spl5_19)),
% 0.21/0.51    inference(resolution,[],[f151,f68])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)) ) | ~spl5_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f150])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ~spl5_6 | spl5_21 | ~spl5_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f158,f59,f161,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl5_6 <=> v1_funct_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_5),
% 0.21/0.51    inference(resolution,[],[f41,f60])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ~spl5_6 | spl5_19 | ~spl5_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f146,f59,f150,f63])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_5),
% 0.21/0.51    inference(resolution,[],[f39,f60])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~spl5_5 | spl5_17 | ~spl5_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f130,f121,f133,f59])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl5_15 <=> sK2 = k7_relset_1(sK1,sK2,sK4,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    sK2 = k9_relat_1(sK4,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_15),
% 0.21/0.51    inference(superposition,[],[f38,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    sK2 = k7_relset_1(sK1,sK2,sK4,sK1) | ~spl5_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f121])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl5_15 | ~spl5_3 | ~spl5_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f119,f59,f51,f121])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    spl5_3 <=> sK2 = k2_relset_1(sK1,sK2,sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    sK2 = k7_relset_1(sK1,sK2,sK4,sK1) | (~spl5_3 | ~spl5_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f117,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    sK2 = k2_relset_1(sK1,sK2,sK4) | ~spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f51])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    k2_relset_1(sK1,sK2,sK4) = k7_relset_1(sK1,sK2,sK4,sK1) | ~spl5_5),
% 0.21/0.51    inference(resolution,[],[f36,f60])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ~spl5_7 | spl5_13),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    $false | (~spl5_7 | spl5_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f68,f105])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_13),
% 0.21/0.51    inference(resolution,[],[f100,f34])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ~v1_relat_1(sK3) | spl5_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl5_13 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ~spl5_13 | spl5_14 | ~spl5_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f97,f83,f102,f99])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl5_10 <=> sK1 = k2_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,sK1) | ~v1_relat_1(X0) | ~v1_relat_1(sK3)) ) | ~spl5_10),
% 0.21/0.51    inference(superposition,[],[f33,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK3) | ~spl5_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl5_10 | ~spl5_4 | ~spl5_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f81,f67,f55,f83])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl5_4 <=> sK1 = k2_relset_1(sK0,sK1,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    sK1 = k2_relat_1(sK3) | (~spl5_4 | ~spl5_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f75,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    sK1 = k2_relset_1(sK0,sK1,sK3) | ~spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f55])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl5_7),
% 0.21/0.51    inference(resolution,[],[f35,f68])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl5_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f25,f71])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,sK4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f23,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,X4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ? [X4] : (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,X4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(X4)) => (sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & k1_xboole_0 != sK2 & sK2 = k2_relset_1(sK1,sK2,sK4) & sK1 = k2_relset_1(sK0,sK1,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2 & k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2 & k1_xboole_0 != X2) & (k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X1,X2,X4) = X2 & k2_relset_1(X0,X1,X3) = X1) => (k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 | k1_xboole_0 = X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_2)).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl5_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f67])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl5_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl5_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f59])).
% 0.21/0.51  % (4167)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f55])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    sK1 = k2_relset_1(sK0,sK1,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f51])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    sK2 = k2_relset_1(sK1,sK2,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ~spl5_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f43])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (4154)------------------------------
% 0.21/0.51  % (4154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4154)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (4154)Memory used [KB]: 11001
% 0.21/0.51  % (4154)Time elapsed: 0.073 s
% 0.21/0.51  % (4154)------------------------------
% 0.21/0.51  % (4154)------------------------------
% 0.21/0.51  % (4165)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (4149)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (4157)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (4147)Success in time 0.154 s
%------------------------------------------------------------------------------
