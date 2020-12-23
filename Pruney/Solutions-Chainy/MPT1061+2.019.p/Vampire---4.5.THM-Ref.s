%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 284 expanded)
%              Number of leaves         :   31 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  441 ( 919 expanded)
%              Number of equality atoms :   69 (  98 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f374,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f104,f108,f115,f122,f127,f134,f142,f148,f160,f211,f319,f348,f373])).

fof(f373,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_17
    | spl5_24 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_17
    | spl5_24 ),
    inference(subsumption_resolution,[],[f371,f370])).

fof(f370,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_11
    | spl5_24 ),
    inference(subsumption_resolution,[],[f369,f318])).

fof(f318,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl5_24 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl5_24
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f369,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f361,f135])).

fof(f135,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK4,X0))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(superposition,[],[f95,f98])).

fof(f98,plain,
    ( ! [X2] : k2_partfun1(sK0,sK3,sK4,X2) = k7_relat_1(sK4,X2)
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f88,f68])).

fof(f68,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f88,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK4)
        | k2_partfun1(sK0,sK3,sK4,X2) = k7_relat_1(sK4,X2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f84,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f84,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f95,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f86,f68])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f84,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f361,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_11 ),
    inference(resolution,[],[f347,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

fof(f347,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_11
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f371,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_11
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f364,f210])).

fof(f210,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl5_17
  <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f364,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_11 ),
    inference(resolution,[],[f347,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f348,plain,
    ( spl5_11
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f312,f113,f102,f83,f67,f125])).

fof(f102,plain,
    ( spl5_6
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f113,plain,
    ( spl5_8
  <=> r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f312,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(resolution,[],[f196,f114])).

fof(f114,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k9_relat_1(sK4,X0),X1)
        | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f130,f195])).

fof(f195,plain,
    ( ! [X12] : v1_relat_1(k7_relat_1(sK4,X12))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f194,f98])).

fof(f194,plain,
    ( ! [X12] : v1_relat_1(k2_partfun1(sK0,sK3,sK4,X12))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f177,f50])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f177,plain,
    ( ! [X12] :
        ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK3))
        | v1_relat_1(k2_partfun1(sK0,sK3,sK4,X12)) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f97,f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f97,plain,
    ( ! [X1] : m1_subset_1(k2_partfun1(sK0,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f87,f68])).

fof(f87,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK4)
        | m1_subset_1(k2_partfun1(sK0,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) )
    | ~ spl5_5 ),
    inference(resolution,[],[f84,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k9_relat_1(sK4,X0),X1)
        | ~ v1_relat_1(k7_relat_1(sK4,X0))
        | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f128,f110])).

fof(f110,plain,
    ( ! [X0] : k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0))
    | ~ spl5_6 ),
    inference(resolution,[],[f103,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f103,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(sK4,X0))
        | ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),X1)
        | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_6 ),
    inference(resolution,[],[f111,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f111,plain,
    ( ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X1)),X1)
    | ~ spl5_6 ),
    inference(resolution,[],[f103,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f27])).

% (18474)Refutation not found, incomplete strategy% (18474)------------------------------
% (18474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18474)Termination reason: Refutation not found, incomplete strategy

% (18474)Memory used [KB]: 10618
% (18474)Time elapsed: 0.082 s
% (18474)------------------------------
% (18474)------------------------------
fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f319,plain,
    ( ~ spl5_24
    | ~ spl5_1
    | ~ spl5_5
    | spl5_10 ),
    inference(avatar_split_clause,[],[f315,f120,f83,f67,f317])).

fof(f120,plain,
    ( spl5_10
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f315,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_1
    | ~ spl5_5
    | spl5_10 ),
    inference(forward_demodulation,[],[f121,f98])).

fof(f121,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f211,plain,
    ( spl5_17
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f167,f144,f102,f75,f209])).

fof(f75,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f144,plain,
    ( spl5_15
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f167,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_15 ),
    inference(resolution,[],[f163,f76])).

fof(f76,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k1_relat_1(k7_relat_1(sK4,X0)) = X0 )
    | ~ spl5_6
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f161,f103])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK4)
        | k1_relat_1(k7_relat_1(sK4,X0)) = X0 )
    | ~ spl5_15 ),
    inference(superposition,[],[f47,f145])).

fof(f145,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f160,plain,
    ( spl5_2
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl5_2
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f152,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f152,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | ~ spl5_14 ),
    inference(superposition,[],[f72,f141])).

fof(f141,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_14
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f72,plain,
    ( ~ v1_xboole_0(sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_2
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f148,plain,
    ( spl5_15
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f146,f137,f132,f144])).

fof(f132,plain,
    ( spl5_12
  <=> k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f137,plain,
    ( spl5_13
  <=> sK0 = k1_relset_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f146,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(superposition,[],[f138,f133])).

fof(f133,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f138,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f142,plain,
    ( spl5_13
    | spl5_14
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f99,f83,f79,f140,f137])).

fof(f79,plain,
    ( spl5_4
  <=> v1_funct_2(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f99,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f92,f80])).

fof(f80,plain,
    ( v1_funct_2(sK4,sK0,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f92,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK4,sK0,sK3)
    | ~ spl5_5 ),
    inference(resolution,[],[f84,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f134,plain,
    ( spl5_12
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f93,f83,f132])).

fof(f93,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f84,f60])).

fof(f127,plain,
    ( ~ spl5_11
    | ~ spl5_1
    | ~ spl5_5
    | spl5_9 ),
    inference(avatar_split_clause,[],[f123,f117,f83,f67,f125])).

fof(f117,plain,
    ( spl5_9
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f123,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1
    | ~ spl5_5
    | spl5_9 ),
    inference(forward_demodulation,[],[f118,f98])).

fof(f118,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f122,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f96,f83,f67,f120,f117])).

fof(f96,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f35,f95])).

fof(f35,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

% (18465)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

fof(f115,plain,
    ( spl5_8
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f109,f106,f83,f113])).

fof(f106,plain,
    ( spl5_7
  <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f109,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f107,f89])).

fof(f89,plain,
    ( ! [X3] : k7_relset_1(sK0,sK3,sK4,X3) = k9_relat_1(sK4,X3)
    | ~ spl5_5 ),
    inference(resolution,[],[f84,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f107,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f40,f106])).

fof(f40,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f104,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f100,f83,f102])).

fof(f100,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f94,f50])).

fof(f94,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK3))
    | v1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f84,f49])).

fof(f85,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f38,f83])).

fof(f38,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f37,f79])).

fof(f37,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f41,f71])).

fof(f41,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (18454)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (18469)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (18454)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (18461)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (18464)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (18462)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (18474)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (18456)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (18459)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (18460)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (18466)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f104,f108,f115,f122,f127,f134,f142,f148,f160,f211,f319,f348,f373])).
% 0.21/0.49  fof(f373,plain,(
% 0.21/0.49    ~spl5_1 | ~spl5_5 | ~spl5_11 | ~spl5_17 | spl5_24),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f372])).
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    $false | (~spl5_1 | ~spl5_5 | ~spl5_11 | ~spl5_17 | spl5_24)),
% 0.21/0.49    inference(subsumption_resolution,[],[f371,f370])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | (~spl5_1 | ~spl5_5 | ~spl5_11 | spl5_24)),
% 0.21/0.49    inference(subsumption_resolution,[],[f369,f318])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl5_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f317])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    spl5_24 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl5_1 | ~spl5_5 | ~spl5_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f361,f135])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.49    inference(superposition,[],[f95,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X2] : (k2_partfun1(sK0,sK3,sK4,X2) = k7_relat_1(sK4,X2)) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f88,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    v1_funct_1(sK4) | ~spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl5_1 <=> v1_funct_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X2] : (~v1_funct_1(sK4) | k2_partfun1(sK0,sK3,sK4,X2) = k7_relat_1(sK4,X2)) ) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f84,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl5_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f68])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(sK4) | v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))) ) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f84,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.49  fof(f361,plain,(
% 0.21/0.49    ~v1_funct_1(k7_relat_1(sK4,sK1)) | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~spl5_11),
% 0.21/0.49    inference(resolution,[],[f347,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).
% 0.21/0.49  fof(f347,plain,(
% 0.21/0.49    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl5_11 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.49  fof(f371,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | (~spl5_11 | ~spl5_17)),
% 0.21/0.49    inference(forward_demodulation,[],[f364,f210])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | ~spl5_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f209])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    spl5_17 <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.49  fof(f364,plain,(
% 0.21/0.49    k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl5_11),
% 0.21/0.49    inference(resolution,[],[f347,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f348,plain,(
% 0.21/0.49    spl5_11 | ~spl5_1 | ~spl5_5 | ~spl5_6 | ~spl5_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f312,f113,f102,f83,f67,f125])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl5_6 <=> v1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    spl5_8 <=> r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl5_1 | ~spl5_5 | ~spl5_6 | ~spl5_8)),
% 0.21/0.49    inference(resolution,[],[f196,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~spl5_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f113])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK4,X0),X1) | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_1 | ~spl5_5 | ~spl5_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f195])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ( ! [X12] : (v1_relat_1(k7_relat_1(sK4,X12))) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.49    inference(forward_demodulation,[],[f194,f98])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    ( ! [X12] : (v1_relat_1(k2_partfun1(sK0,sK3,sK4,X12))) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f177,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    ( ! [X12] : (~v1_relat_1(k2_zfmisc_1(sK0,sK3)) | v1_relat_1(k2_partfun1(sK0,sK3,sK4,X12))) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.49    inference(resolution,[],[f97,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X1] : (m1_subset_1(k2_partfun1(sK0,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) ) | (~spl5_1 | ~spl5_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f68])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(sK4) | m1_subset_1(k2_partfun1(sK0,sK3,sK4,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) ) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f84,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK4,X0),X1) | ~v1_relat_1(k7_relat_1(sK4,X0)) | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_6),
% 0.21/0.49    inference(forward_demodulation,[],[f128,f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0] : (k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0))) ) | ~spl5_6),
% 0.21/0.49    inference(resolution,[],[f103,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    v1_relat_1(sK4) | ~spl5_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f102])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(sK4,X0)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),X1) | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_6),
% 0.21/0.49    inference(resolution,[],[f111,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X1)),X1)) ) | ~spl5_6),
% 0.21/0.49    inference(resolution,[],[f103,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  % (18474)Refutation not found, incomplete strategy% (18474)------------------------------
% 0.21/0.49  % (18474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18474)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (18474)Memory used [KB]: 10618
% 0.21/0.49  % (18474)Time elapsed: 0.082 s
% 0.21/0.49  % (18474)------------------------------
% 0.21/0.49  % (18474)------------------------------
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.49  fof(f319,plain,(
% 0.21/0.49    ~spl5_24 | ~spl5_1 | ~spl5_5 | spl5_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f315,f120,f83,f67,f317])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl5_10 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl5_1 | ~spl5_5 | spl5_10)),
% 0.21/0.49    inference(forward_demodulation,[],[f121,f98])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    spl5_17 | ~spl5_3 | ~spl5_6 | ~spl5_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f167,f144,f102,f75,f209])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl5_3 <=> r1_tarski(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    spl5_15 <=> sK0 = k1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_3 | ~spl5_6 | ~spl5_15)),
% 0.21/0.49    inference(resolution,[],[f163,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    r1_tarski(sK1,sK0) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_relat_1(k7_relat_1(sK4,X0)) = X0) ) | (~spl5_6 | ~spl5_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f161,f103])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_relat_1(sK4) | k1_relat_1(k7_relat_1(sK4,X0)) = X0) ) | ~spl5_15),
% 0.21/0.49    inference(superposition,[],[f47,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK4) | ~spl5_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f144])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    spl5_2 | ~spl5_14),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f159])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    $false | (spl5_2 | ~spl5_14)),
% 0.21/0.49    inference(subsumption_resolution,[],[f152,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | ~spl5_14)),
% 0.21/0.49    inference(superposition,[],[f72,f141])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | ~spl5_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl5_14 <=> k1_xboole_0 = sK3),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~v1_xboole_0(sK3) | spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl5_2 <=> v1_xboole_0(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl5_15 | ~spl5_12 | ~spl5_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f146,f137,f132,f144])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl5_12 <=> k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl5_13 <=> sK0 = k1_relset_1(sK0,sK3,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK4) | (~spl5_12 | ~spl5_13)),
% 0.21/0.49    inference(superposition,[],[f138,f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) | ~spl5_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f132])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK3,sK4) | ~spl5_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl5_13 | spl5_14 | ~spl5_4 | ~spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f99,f83,f79,f140,f137])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    spl5_4 <=> v1_funct_2(sK4,sK0,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | (~spl5_4 | ~spl5_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f92,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    v1_funct_2(sK4,sK0,sK3) | ~spl5_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f79])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | ~v1_funct_2(sK4,sK0,sK3) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f84,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl5_12 | ~spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f93,f83,f132])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f84,f60])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ~spl5_11 | ~spl5_1 | ~spl5_5 | spl5_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f123,f117,f83,f67,f125])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl5_9 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl5_1 | ~spl5_5 | spl5_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f118,f98])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f117])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ~spl5_9 | ~spl5_10 | ~spl5_1 | ~spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f96,f83,f67,f120,f117])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl5_1 | ~spl5_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f35,f95])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  % (18465)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f14])).
% 0.21/0.49  fof(f14,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl5_8 | ~spl5_5 | ~spl5_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f109,f106,f83,f113])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl5_7 <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    r1_tarski(k9_relat_1(sK4,sK1),sK2) | (~spl5_5 | ~spl5_7)),
% 0.21/0.49    inference(forward_demodulation,[],[f107,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X3] : (k7_relset_1(sK0,sK3,sK4,X3) = k9_relat_1(sK4,X3)) ) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f84,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) | ~spl5_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f106])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl5_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f106])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl5_6 | ~spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f100,f83,f102])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    v1_relat_1(sK4) | ~spl5_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f50])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK3)) | v1_relat_1(sK4) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f84,f49])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl5_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f83])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f79])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v1_funct_2(sK4,sK0,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f75])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    r1_tarski(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f71])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ~v1_xboole_0(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f67])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    v1_funct_1(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18454)------------------------------
% 0.21/0.49  % (18454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18454)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18454)Memory used [KB]: 6396
% 0.21/0.49  % (18454)Time elapsed: 0.063 s
% 0.21/0.49  % (18454)------------------------------
% 0.21/0.49  % (18454)------------------------------
% 0.21/0.50  % (18451)Success in time 0.138 s
%------------------------------------------------------------------------------
