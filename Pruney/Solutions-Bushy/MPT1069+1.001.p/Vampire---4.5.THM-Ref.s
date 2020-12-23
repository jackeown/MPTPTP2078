%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1069+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 328 expanded)
%              Number of leaves         :   46 ( 156 expanded)
%              Depth                    :    9
%              Number of atoms          :  572 (1728 expanded)
%              Number of equality atoms :   81 ( 341 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f73,f77,f81,f85,f89,f93,f97,f101,f105,f110,f121,f145,f146,f154,f166,f169,f172,f180,f197,f201,f202,f208,f223,f230,f241,f259])).

fof(f259,plain,
    ( ~ spl6_4
    | ~ spl6_11
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f76,f255])).

fof(f255,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK1)
    | ~ spl6_11
    | ~ spl6_24
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f196,f251])).

fof(f251,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl6_11
    | ~ spl6_29 ),
    inference(resolution,[],[f240,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,o_0_0_xboole_0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl6_11 ),
    inference(resolution,[],[f111,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl6_11 ),
    inference(resolution,[],[f60,f104])).

fof(f104,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_11
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f240,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),o_0_0_xboole_0)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl6_29
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3)) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl6_24
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f76,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f241,plain,
    ( spl6_29
    | ~ spl6_13
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f233,f228,f119,f239])).

fof(f119,plain,
    ( spl6_13
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f228,plain,
    ( spl6_27
  <=> o_0_0_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f233,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),o_0_0_xboole_0)
    | ~ spl6_13
    | ~ spl6_27 ),
    inference(superposition,[],[f120,f229])).

fof(f229,plain,
    ( o_0_0_xboole_0 = k1_relat_1(sK4)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f228])).

fof(f120,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f230,plain,
    ( spl6_27
    | ~ spl6_12
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f226,f178,f108,f228])).

fof(f108,plain,
    ( spl6_12
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f178,plain,
    ( spl6_21
  <=> v1_xboole_0(k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f226,plain,
    ( o_0_0_xboole_0 = k1_relat_1(sK4)
    | ~ spl6_12
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f225,f109])).

fof(f109,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f225,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl6_21 ),
    inference(resolution,[],[f179,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f179,plain,
    ( v1_xboole_0(k1_relat_1(sK4))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f178])).

fof(f223,plain,
    ( spl6_20
    | ~ spl6_13
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f216,f206,f119,f175])).

fof(f175,plain,
    ( spl6_20
  <=> m1_subset_1(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f206,plain,
    ( spl6_25
  <=> r2_hidden(k1_funct_1(sK3,sK5),k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f216,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ spl6_13
    | ~ spl6_25 ),
    inference(resolution,[],[f213,f120])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | m1_subset_1(k1_funct_1(sK3,sK5),X0) )
    | ~ spl6_25 ),
    inference(resolution,[],[f211,f54])).

fof(f211,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(X3))
        | m1_subset_1(k1_funct_1(sK3,sK5),X3) )
    | ~ spl6_25 ),
    inference(resolution,[],[f207,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f207,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k2_relset_1(sK1,sK2,sK3))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f206])).

fof(f208,plain,
    ( spl6_25
    | ~ spl6_4
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f204,f195,f75,f206])).

fof(f204,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k2_relset_1(sK1,sK2,sK3))
    | ~ spl6_4
    | ~ spl6_24 ),
    inference(resolution,[],[f196,f76])).

fof(f202,plain,
    ( o_0_0_xboole_0 != sK2
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f201,plain,
    ( spl6_15
    | ~ spl6_12
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f200,f189,f108,f143])).

fof(f143,plain,
    ( spl6_15
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f189,plain,
    ( spl6_22
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f200,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl6_12
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f199,f109])).

fof(f199,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_22 ),
    inference(resolution,[],[f190,f50])).

fof(f190,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f189])).

fof(f197,plain,
    ( spl6_22
    | ~ spl6_9
    | spl6_23
    | ~ spl6_7
    | spl6_24
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f187,f108,f91,f195,f87,f192,f95,f189])).

fof(f95,plain,
    ( spl6_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f192,plain,
    ( spl6_23
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f87,plain,
    ( spl6_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f91,plain,
    ( spl6_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f187,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(sK1,sK2,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | o_0_0_xboole_0 = sK2
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(resolution,[],[f130,f92])).

fof(f92,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f130,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(X1,X3,X0)
        | r2_hidden(k1_funct_1(X1,X2),k2_relset_1(X3,X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
        | o_0_0_xboole_0 = X0
        | ~ v1_funct_1(X1)
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X2,X3) )
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f129,f109])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | r2_hidden(k1_funct_1(X1,X2),k2_relset_1(X3,X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_2(X1,X3,X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f61,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f180,plain,
    ( ~ spl6_20
    | spl6_21
    | spl6_19 ),
    inference(avatar_split_clause,[],[f173,f164,f178,f175])).

fof(f164,plain,
    ( spl6_19
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f173,plain,
    ( v1_xboole_0(k1_relat_1(sK4))
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl6_19 ),
    inference(resolution,[],[f165,f51])).

fof(f165,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f164])).

fof(f172,plain,
    ( ~ spl6_5
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl6_5
    | spl6_18 ),
    inference(subsumption_resolution,[],[f80,f170])).

fof(f170,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl6_18 ),
    inference(resolution,[],[f162,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f162,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl6_18
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f80,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f169,plain,
    ( ~ spl6_5
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl6_5
    | spl6_17 ),
    inference(subsumption_resolution,[],[f80,f167])).

fof(f167,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_17 ),
    inference(resolution,[],[f159,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f159,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl6_17
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f166,plain,
    ( ~ spl6_17
    | ~ spl6_18
    | ~ spl6_6
    | ~ spl6_19
    | spl6_16 ),
    inference(avatar_split_clause,[],[f156,f152,f164,f83,f161,f158])).

fof(f83,plain,
    ( spl6_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f152,plain,
    ( spl6_16
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f156,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl6_16 ),
    inference(trivial_inequality_removal,[],[f155])).

fof(f155,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl6_16 ),
    inference(superposition,[],[f153,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f153,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_3
    | ~ spl6_16
    | spl6_1
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f147,f140,f63,f152,f71,f83,f79,f75])).

fof(f71,plain,
    ( spl6_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f63,plain,
    ( spl6_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f140,plain,
    ( spl6_14
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ m1_subset_1(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f147,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | spl6_1
    | ~ spl6_14 ),
    inference(superposition,[],[f64,f141])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ m1_subset_1(X2,sK1) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f64,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f146,plain,
    ( o_0_0_xboole_0 != sK1
    | o_0_0_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f145,plain,
    ( spl6_10
    | ~ spl6_9
    | ~ spl6_7
    | spl6_14
    | spl6_15
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f135,f108,f91,f143,f140,f87,f95,f99])).

fof(f99,plain,
    ( spl6_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = sK1
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
        | ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK2) )
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f134,f109])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = sK1
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
        | ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK2) )
    | ~ spl6_8 ),
    inference(resolution,[],[f55,f92])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

% (21850)Refutation not found, incomplete strategy% (21850)------------------------------
% (21850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21865)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (21848)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f121,plain,
    ( ~ spl6_5
    | spl6_13
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f116,f71,f119,f79])).

fof(f116,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_3 ),
    inference(superposition,[],[f72,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f72,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f110,plain,
    ( spl6_12
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f106,f103,f108])).

fof(f106,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_11 ),
    inference(resolution,[],[f50,f104])).

fof(f105,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f49,f103])).

fof(f49,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f101,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f39,f99])).

fof(f39,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f97,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f40,f95])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f41,f91])).

fof(f41,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f42,f87])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f43,f83])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f45,f75])).

fof(f45,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f46,f71])).

fof(f46,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f47,f67])).

fof(f67,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f47,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f48,f63])).

fof(f48,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f37])).

%------------------------------------------------------------------------------
