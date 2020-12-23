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
% DateTime   : Thu Dec  3 13:07:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 330 expanded)
%              Number of leaves         :   50 ( 144 expanded)
%              Depth                    :    8
%              Number of atoms          :  708 (1344 expanded)
%              Number of equality atoms :  113 ( 221 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f504,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f93,f97,f101,f105,f109,f113,f117,f121,f129,f137,f141,f145,f150,f159,f165,f171,f207,f221,f228,f241,f256,f260,f264,f279,f307,f366,f432,f444,f465,f472,f480,f494,f503])).

fof(f503,plain,
    ( spl6_5
    | ~ spl6_13
    | ~ spl6_76 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | spl6_5
    | ~ spl6_13
    | ~ spl6_76 ),
    inference(subsumption_resolution,[],[f500,f88])).

fof(f88,plain,
    ( k1_xboole_0 != sK1
    | spl6_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f500,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_13
    | ~ spl6_76 ),
    inference(resolution,[],[f493,f120])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_13
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f493,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl6_76
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f494,plain,
    ( spl6_76
    | ~ spl6_4
    | ~ spl6_18
    | spl6_72 ),
    inference(avatar_split_clause,[],[f484,f463,f139,f83,f492])).

% (12191)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (12192)Refutation not found, incomplete strategy% (12192)------------------------------
% (12192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12192)Termination reason: Refutation not found, incomplete strategy

% (12192)Memory used [KB]: 10618
% (12192)Time elapsed: 0.108 s
% (12192)------------------------------
% (12192)------------------------------
fof(f83,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f139,plain,
    ( spl6_18
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f463,plain,
    ( spl6_72
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f484,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_4
    | ~ spl6_18
    | spl6_72 ),
    inference(subsumption_resolution,[],[f483,f84])).

fof(f84,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f483,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | ~ spl6_18
    | spl6_72 ),
    inference(resolution,[],[f464,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f139])).

fof(f464,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl6_72 ),
    inference(avatar_component_clause,[],[f463])).

fof(f480,plain,
    ( ~ spl6_7
    | ~ spl6_19
    | spl6_71 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_19
    | spl6_71 ),
    inference(unit_resulting_resolution,[],[f96,f461,f144])).

fof(f144,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_19
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f461,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_71 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl6_71
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f96,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f472,plain,
    ( ~ spl6_8
    | ~ spl6_19
    | spl6_70 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_19
    | spl6_70 ),
    inference(unit_resulting_resolution,[],[f100,f458,f144])).

fof(f458,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_70 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl6_70
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f100,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f465,plain,
    ( ~ spl6_70
    | ~ spl6_71
    | ~ spl6_72
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_33
    | ~ spl6_36
    | spl6_68 ),
    inference(avatar_split_clause,[],[f450,f442,f254,f219,f75,f71,f463,f460,f457])).

fof(f71,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f75,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f219,plain,
    ( spl6_33
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f254,plain,
    ( spl6_36
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f442,plain,
    ( spl6_68
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f450,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_33
    | ~ spl6_36
    | spl6_68 ),
    inference(forward_demodulation,[],[f449,f255])).

fof(f255,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f254])).

fof(f449,plain,
    ( ~ v1_relat_1(sK4)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_33
    | spl6_68 ),
    inference(subsumption_resolution,[],[f448,f72])).

fof(f72,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f448,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_2
    | ~ spl6_33
    | spl6_68 ),
    inference(subsumption_resolution,[],[f447,f76])).

fof(f76,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f447,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_33
    | spl6_68 ),
    inference(trivial_inequality_removal,[],[f446])).

fof(f446,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_33
    | spl6_68 ),
    inference(superposition,[],[f443,f220])).

fof(f220,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f219])).

fof(f443,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl6_68 ),
    inference(avatar_component_clause,[],[f442])).

fof(f444,plain,
    ( ~ spl6_68
    | ~ spl6_7
    | ~ spl6_9
    | spl6_12
    | ~ spl6_66 ),
    inference(avatar_split_clause,[],[f436,f430,f115,f103,f95,f442])).

fof(f103,plain,
    ( spl6_9
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f115,plain,
    ( spl6_12
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f430,plain,
    ( spl6_66
  <=> ! [X1] :
        ( k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f436,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | ~ spl6_7
    | ~ spl6_9
    | spl6_12
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f435,f96])).

fof(f435,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_9
    | spl6_12
    | ~ spl6_66 ),
    inference(subsumption_resolution,[],[f434,f104])).

fof(f104,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f434,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | spl6_12
    | ~ spl6_66 ),
    inference(superposition,[],[f116,f431])).

fof(f431,plain,
    ( ! [X1] :
        ( k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
    | ~ spl6_66 ),
    inference(avatar_component_clause,[],[f430])).

fof(f116,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f432,plain,
    ( spl6_66
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_37
    | ~ spl6_55 ),
    inference(avatar_split_clause,[],[f375,f364,f258,f99,f75,f71,f430])).

fof(f258,plain,
    ( spl6_37
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f364,plain,
    ( spl6_55
  <=> ! [X0] :
        ( k8_funct_2(sK1,sK2,X0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,X0,sK3,sK4)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f375,plain,
    ( ! [X1] :
        ( k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_37
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f374,f76])).

fof(f374,plain,
    ( ! [X1] :
        ( k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_37
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f373,f72])).

fof(f373,plain,
    ( ! [X1] :
        ( k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(sK3) )
    | ~ spl6_8
    | ~ spl6_37
    | ~ spl6_55 ),
    inference(subsumption_resolution,[],[f372,f100])).

fof(f372,plain,
    ( ! [X1] :
        ( k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ v1_funct_1(sK3) )
    | ~ spl6_37
    | ~ spl6_55 ),
    inference(duplicate_literal_removal,[],[f369])).

fof(f369,plain,
    ( ! [X1] :
        ( k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl6_37
    | ~ spl6_55 ),
    inference(superposition,[],[f365,f259])).

fof(f259,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X4) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f258])).

fof(f365,plain,
    ( ! [X0] :
        ( k8_funct_2(sK1,sK2,X0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,X0,sK3,sK4)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) )
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f364])).

fof(f366,plain,
    ( spl6_55
    | ~ spl6_1
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f309,f305,f71,f364])).

fof(f305,plain,
    ( spl6_46
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f309,plain,
    ( ! [X0] :
        ( k8_funct_2(sK1,sK2,X0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,X0,sK3,sK4)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) )
    | ~ spl6_1
    | ~ spl6_46 ),
    inference(resolution,[],[f306,f72])).

fof(f306,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) )
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f305])).

fof(f307,plain,
    ( spl6_35
    | spl6_46
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f283,f277,f99,f91,f305,f226])).

fof(f226,plain,
    ( spl6_35
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f91,plain,
    ( spl6_6
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f277,plain,
    ( spl6_41
  <=> ! [X5,X7,X4,X6] :
        ( ~ v1_funct_2(sK3,X4,X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X7)))
        | ~ r1_tarski(k2_relset_1(X4,X5,sK3),k1_relset_1(X5,X7,X6))
        | k1_xboole_0 = X5
        | k8_funct_2(X4,X5,X7,sK3,X6) = k1_partfun1(X4,X5,X5,X7,sK3,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f283,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0))
        | k1_xboole_0 = sK2
        | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f282,f100])).

fof(f282,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0))
        | k1_xboole_0 = sK2
        | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) )
    | ~ spl6_6
    | ~ spl6_41 ),
    inference(resolution,[],[f278,f92])).

fof(f92,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f278,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_2(sK3,X4,X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X7)))
        | ~ r1_tarski(k2_relset_1(X4,X5,sK3),k1_relset_1(X5,X7,X6))
        | k1_xboole_0 = X5
        | k8_funct_2(X4,X5,X7,sK3,X6) = k1_partfun1(X4,X5,X5,X7,sK3,X6) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f277])).

fof(f279,plain,
    ( spl6_41
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f266,f262,f75,f277])).

fof(f262,plain,
    ( spl6_38
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
        | k1_xboole_0 = X1
        | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f266,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_funct_2(sK3,X4,X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X7)))
        | ~ r1_tarski(k2_relset_1(X4,X5,sK3),k1_relset_1(X5,X7,X6))
        | k1_xboole_0 = X5
        | k8_funct_2(X4,X5,X7,sK3,X6) = k1_partfun1(X4,X5,X5,X7,sK3,X6) )
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(resolution,[],[f263,f76])).

fof(f263,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
        | k1_xboole_0 = X1
        | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) )
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f262])).

fof(f264,plain,(
    spl6_38 ),
    inference(avatar_split_clause,[],[f62,f262])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | k1_xboole_0 = X1
      | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

fof(f260,plain,(
    spl6_37 ),
    inference(avatar_split_clause,[],[f63,f258])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f256,plain,
    ( spl6_36
    | ~ spl6_8
    | ~ spl6_23
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f251,f223,f163,f99,f254])).

fof(f163,plain,
    ( spl6_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f223,plain,
    ( spl6_34
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f251,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_8
    | ~ spl6_23
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f247,f100])).

fof(f247,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_23
    | ~ spl6_34 ),
    inference(superposition,[],[f224,f164])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f163])).

fof(f224,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f223])).

fof(f241,plain,
    ( ~ spl6_11
    | spl6_24
    | ~ spl6_35 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl6_11
    | spl6_24
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f235,f112])).

fof(f112,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_11
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f235,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl6_24
    | ~ spl6_35 ),
    inference(backward_demodulation,[],[f170,f227])).

fof(f227,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f226])).

fof(f170,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl6_24
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f228,plain,
    ( spl6_34
    | spl6_35
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f216,f205,f99,f91,f226,f223])).

fof(f205,plain,
    ( spl6_31
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f216,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f214,f100])).

fof(f214,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_6
    | ~ spl6_31 ),
    inference(resolution,[],[f206,f92])).

fof(f206,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f205])).

fof(f221,plain,(
    spl6_33 ),
    inference(avatar_split_clause,[],[f50,f219])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f207,plain,(
    spl6_31 ),
    inference(avatar_split_clause,[],[f60,f205])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f171,plain,
    ( ~ spl6_24
    | spl6_3
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f160,f157,f79,f169])).

fof(f79,plain,
    ( spl6_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f157,plain,
    ( spl6_22
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f160,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl6_3
    | ~ spl6_22 ),
    inference(resolution,[],[f158,f80])).

fof(f80,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f158,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f157])).

fof(f165,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f54,f163])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f159,plain,
    ( spl6_22
    | ~ spl6_15
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f151,f148,f127,f157])).

fof(f127,plain,
    ( spl6_15
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f148,plain,
    ( spl6_20
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f151,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl6_15
    | ~ spl6_20 ),
    inference(resolution,[],[f149,f128])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f127])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f148])).

fof(f150,plain,
    ( spl6_20
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f146,f135,f107,f148])).

fof(f107,plain,
    ( spl6_10
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f135,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( v1_xboole_0(X1)
        | ~ r1_tarski(X1,X0)
        | ~ r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(resolution,[],[f136,f108])).

fof(f108,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X1,X0)
        | ~ r1_tarski(X1,X0)
        | v1_xboole_0(X1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f135])).

fof(f145,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f53,f143])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f141,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f49,f139])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f137,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f48,f135])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f129,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f52,f127])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f121,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f47,f119])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f117,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f38,f115])).

fof(f38,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
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
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f113,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f46,f111])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f109,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f45,f107])).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f105,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f36,f103])).

fof(f36,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f43,f99])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f40,f95])).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f93,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f42,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f37,f87])).

fof(f37,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f35,f83])).

fof(f35,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f41,f75])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f39,f71])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:25:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (12177)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (12178)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (12185)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (12186)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (12185)Refutation not found, incomplete strategy% (12185)------------------------------
% 0.22/0.49  % (12185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12190)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (12185)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12185)Memory used [KB]: 1791
% 0.22/0.50  % (12185)Time elapsed: 0.075 s
% 0.22/0.50  % (12185)------------------------------
% 0.22/0.50  % (12185)------------------------------
% 0.22/0.51  % (12188)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (12183)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (12184)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (12174)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (12172)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (12189)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (12173)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (12183)Refutation not found, incomplete strategy% (12183)------------------------------
% 0.22/0.51  % (12183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12183)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12183)Memory used [KB]: 10746
% 0.22/0.51  % (12183)Time elapsed: 0.095 s
% 0.22/0.51  % (12183)------------------------------
% 0.22/0.51  % (12183)------------------------------
% 0.22/0.51  % (12173)Refutation not found, incomplete strategy% (12173)------------------------------
% 0.22/0.51  % (12173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12173)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12173)Memory used [KB]: 10618
% 0.22/0.51  % (12173)Time elapsed: 0.097 s
% 0.22/0.51  % (12173)------------------------------
% 0.22/0.51  % (12173)------------------------------
% 0.22/0.51  % (12175)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (12179)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (12176)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (12181)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (12182)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (12180)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (12187)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.53  % (12192)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.53  % (12181)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f504,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f93,f97,f101,f105,f109,f113,f117,f121,f129,f137,f141,f145,f150,f159,f165,f171,f207,f221,f228,f241,f256,f260,f264,f279,f307,f366,f432,f444,f465,f472,f480,f494,f503])).
% 0.22/0.53  fof(f503,plain,(
% 0.22/0.53    spl6_5 | ~spl6_13 | ~spl6_76),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f502])).
% 0.22/0.53  fof(f502,plain,(
% 0.22/0.53    $false | (spl6_5 | ~spl6_13 | ~spl6_76)),
% 0.22/0.53    inference(subsumption_resolution,[],[f500,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | spl6_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl6_5 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.53  fof(f500,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | (~spl6_13 | ~spl6_76)),
% 0.22/0.53    inference(resolution,[],[f493,f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl6_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    spl6_13 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.53  fof(f493,plain,(
% 0.22/0.53    v1_xboole_0(sK1) | ~spl6_76),
% 0.22/0.53    inference(avatar_component_clause,[],[f492])).
% 0.22/0.53  fof(f492,plain,(
% 0.22/0.53    spl6_76 <=> v1_xboole_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).
% 0.22/0.53  fof(f494,plain,(
% 0.22/0.53    spl6_76 | ~spl6_4 | ~spl6_18 | spl6_72),
% 0.22/0.53    inference(avatar_split_clause,[],[f484,f463,f139,f83,f492])).
% 0.22/0.53  % (12191)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  % (12192)Refutation not found, incomplete strategy% (12192)------------------------------
% 0.22/0.53  % (12192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12192)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12192)Memory used [KB]: 10618
% 0.22/0.53  % (12192)Time elapsed: 0.108 s
% 0.22/0.53  % (12192)------------------------------
% 0.22/0.53  % (12192)------------------------------
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl6_4 <=> m1_subset_1(sK5,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    spl6_18 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.53  fof(f463,plain,(
% 0.22/0.53    spl6_72 <=> r2_hidden(sK5,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 0.22/0.53  fof(f484,plain,(
% 0.22/0.53    v1_xboole_0(sK1) | (~spl6_4 | ~spl6_18 | spl6_72)),
% 0.22/0.53    inference(subsumption_resolution,[],[f483,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    m1_subset_1(sK5,sK1) | ~spl6_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f83])).
% 0.22/0.53  fof(f483,plain,(
% 0.22/0.53    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | (~spl6_18 | spl6_72)),
% 0.22/0.53    inference(resolution,[],[f464,f140])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) ) | ~spl6_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f139])).
% 0.22/0.53  fof(f464,plain,(
% 0.22/0.53    ~r2_hidden(sK5,sK1) | spl6_72),
% 0.22/0.53    inference(avatar_component_clause,[],[f463])).
% 0.22/0.53  fof(f480,plain,(
% 0.22/0.53    ~spl6_7 | ~spl6_19 | spl6_71),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f478])).
% 0.22/0.53  fof(f478,plain,(
% 0.22/0.53    $false | (~spl6_7 | ~spl6_19 | spl6_71)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f96,f461,f144])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f143])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    spl6_19 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.53  fof(f461,plain,(
% 0.22/0.53    ~v1_relat_1(sK4) | spl6_71),
% 0.22/0.53    inference(avatar_component_clause,[],[f460])).
% 0.22/0.53  fof(f460,plain,(
% 0.22/0.53    spl6_71 <=> v1_relat_1(sK4)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl6_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl6_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.53  fof(f472,plain,(
% 0.22/0.53    ~spl6_8 | ~spl6_19 | spl6_70),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f470])).
% 0.22/0.53  fof(f470,plain,(
% 0.22/0.53    $false | (~spl6_8 | ~spl6_19 | spl6_70)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f100,f458,f144])).
% 0.22/0.53  fof(f458,plain,(
% 0.22/0.53    ~v1_relat_1(sK3) | spl6_70),
% 0.22/0.53    inference(avatar_component_clause,[],[f457])).
% 0.22/0.53  fof(f457,plain,(
% 0.22/0.53    spl6_70 <=> v1_relat_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl6_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.53  fof(f465,plain,(
% 0.22/0.53    ~spl6_70 | ~spl6_71 | ~spl6_72 | ~spl6_1 | ~spl6_2 | ~spl6_33 | ~spl6_36 | spl6_68),
% 0.22/0.53    inference(avatar_split_clause,[],[f450,f442,f254,f219,f75,f71,f463,f460,f457])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl6_1 <=> v1_funct_1(sK4)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl6_2 <=> v1_funct_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    spl6_33 <=> ! [X1,X0,X2] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.22/0.53  fof(f254,plain,(
% 0.22/0.53    spl6_36 <=> sK1 = k1_relat_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.22/0.53  fof(f442,plain,(
% 0.22/0.53    spl6_68 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 0.22/0.53  fof(f450,plain,(
% 0.22/0.53    ~r2_hidden(sK5,sK1) | ~v1_relat_1(sK4) | ~v1_relat_1(sK3) | (~spl6_1 | ~spl6_2 | ~spl6_33 | ~spl6_36 | spl6_68)),
% 0.22/0.53    inference(forward_demodulation,[],[f449,f255])).
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    sK1 = k1_relat_1(sK3) | ~spl6_36),
% 0.22/0.53    inference(avatar_component_clause,[],[f254])).
% 0.22/0.53  fof(f449,plain,(
% 0.22/0.53    ~v1_relat_1(sK4) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl6_1 | ~spl6_2 | ~spl6_33 | spl6_68)),
% 0.22/0.53    inference(subsumption_resolution,[],[f448,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    v1_funct_1(sK4) | ~spl6_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f71])).
% 0.22/0.53  fof(f448,plain,(
% 0.22/0.53    ~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl6_2 | ~spl6_33 | spl6_68)),
% 0.22/0.53    inference(subsumption_resolution,[],[f447,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    v1_funct_1(sK3) | ~spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f75])).
% 0.22/0.53  fof(f447,plain,(
% 0.22/0.53    ~v1_funct_1(sK3) | ~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl6_33 | spl6_68)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f446])).
% 0.22/0.53  fof(f446,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl6_33 | spl6_68)),
% 0.22/0.53    inference(superposition,[],[f443,f220])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl6_33),
% 0.22/0.53    inference(avatar_component_clause,[],[f219])).
% 0.22/0.53  fof(f443,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | spl6_68),
% 0.22/0.53    inference(avatar_component_clause,[],[f442])).
% 0.22/0.53  fof(f444,plain,(
% 0.22/0.53    ~spl6_68 | ~spl6_7 | ~spl6_9 | spl6_12 | ~spl6_66),
% 0.22/0.53    inference(avatar_split_clause,[],[f436,f430,f115,f103,f95,f442])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl6_9 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    spl6_12 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.53  fof(f430,plain,(
% 0.22/0.53    spl6_66 <=> ! [X1] : (k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 0.22/0.53  fof(f436,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | (~spl6_7 | ~spl6_9 | spl6_12 | ~spl6_66)),
% 0.22/0.53    inference(subsumption_resolution,[],[f435,f96])).
% 0.22/0.53  fof(f435,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | (~spl6_9 | spl6_12 | ~spl6_66)),
% 0.22/0.53    inference(subsumption_resolution,[],[f434,f104])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl6_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f103])).
% 0.22/0.53  fof(f434,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | (spl6_12 | ~spl6_66)),
% 0.22/0.53    inference(superposition,[],[f116,f431])).
% 0.22/0.53  fof(f431,plain,(
% 0.22/0.53    ( ! [X1] : (k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | ~spl6_66),
% 0.22/0.53    inference(avatar_component_clause,[],[f430])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl6_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f115])).
% 0.22/0.53  fof(f432,plain,(
% 0.22/0.53    spl6_66 | ~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_37 | ~spl6_55),
% 0.22/0.53    inference(avatar_split_clause,[],[f375,f364,f258,f99,f75,f71,f430])).
% 0.22/0.53  fof(f258,plain,(
% 0.22/0.53    spl6_37 <=> ! [X1,X3,X5,X0,X2,X4] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.22/0.53  fof(f364,plain,(
% 0.22/0.53    spl6_55 <=> ! [X0] : (k8_funct_2(sK1,sK2,X0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,X0,sK3,sK4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 0.22/0.53  fof(f375,plain,(
% 0.22/0.53    ( ! [X1] : (k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_37 | ~spl6_55)),
% 0.22/0.53    inference(subsumption_resolution,[],[f374,f76])).
% 0.22/0.53  fof(f374,plain,(
% 0.22/0.53    ( ! [X1] : (k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(sK3)) ) | (~spl6_1 | ~spl6_8 | ~spl6_37 | ~spl6_55)),
% 0.22/0.53    inference(subsumption_resolution,[],[f373,f72])).
% 0.22/0.53  fof(f373,plain,(
% 0.22/0.53    ( ! [X1] : (k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(sK4) | ~v1_funct_1(sK3)) ) | (~spl6_8 | ~spl6_37 | ~spl6_55)),
% 0.22/0.53    inference(subsumption_resolution,[],[f372,f100])).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    ( ! [X1] : (k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~v1_funct_1(sK3)) ) | (~spl6_37 | ~spl6_55)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f369])).
% 0.22/0.53  fof(f369,plain,(
% 0.22/0.53    ( ! [X1] : (k5_relat_1(sK3,sK4) = k8_funct_2(sK1,sK2,X1,sK3,sK4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~v1_funct_1(sK3)) ) | (~spl6_37 | ~spl6_55)),
% 0.22/0.53    inference(superposition,[],[f365,f259])).
% 0.22/0.53  fof(f259,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) ) | ~spl6_37),
% 0.22/0.53    inference(avatar_component_clause,[],[f258])).
% 0.22/0.53  fof(f365,plain,(
% 0.22/0.53    ( ! [X0] : (k8_funct_2(sK1,sK2,X0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,X0,sK3,sK4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | ~spl6_55),
% 0.22/0.53    inference(avatar_component_clause,[],[f364])).
% 0.22/0.53  fof(f366,plain,(
% 0.22/0.53    spl6_55 | ~spl6_1 | ~spl6_46),
% 0.22/0.53    inference(avatar_split_clause,[],[f309,f305,f71,f364])).
% 0.22/0.53  fof(f305,plain,(
% 0.22/0.53    spl6_46 <=> ! [X1,X0] : (~v1_funct_1(X0) | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    ( ! [X0] : (k8_funct_2(sK1,sK2,X0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,X0,sK3,sK4) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))) ) | (~spl6_1 | ~spl6_46)),
% 0.22/0.53    inference(resolution,[],[f306,f72])).
% 0.22/0.53  fof(f306,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))) ) | ~spl6_46),
% 0.22/0.53    inference(avatar_component_clause,[],[f305])).
% 0.22/0.53  fof(f307,plain,(
% 0.22/0.53    spl6_35 | spl6_46 | ~spl6_6 | ~spl6_8 | ~spl6_41),
% 0.22/0.53    inference(avatar_split_clause,[],[f283,f277,f99,f91,f305,f226])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    spl6_35 <=> k1_xboole_0 = sK2),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl6_6 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    spl6_41 <=> ! [X5,X7,X4,X6] : (~v1_funct_2(sK3,X4,X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X7))) | ~r1_tarski(k2_relset_1(X4,X5,sK3),k1_relset_1(X5,X7,X6)) | k1_xboole_0 = X5 | k8_funct_2(X4,X5,X7,sK3,X6) = k1_partfun1(X4,X5,X5,X7,sK3,X6))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0)) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0)) ) | (~spl6_6 | ~spl6_8 | ~spl6_41)),
% 0.22/0.53    inference(subsumption_resolution,[],[f282,f100])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X1,X0)) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,X1,sK3,X0) = k1_partfun1(sK1,sK2,sK2,X1,sK3,X0)) ) | (~spl6_6 | ~spl6_41)),
% 0.22/0.53    inference(resolution,[],[f278,f92])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    v1_funct_2(sK3,sK1,sK2) | ~spl6_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f91])).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    ( ! [X6,X4,X7,X5] : (~v1_funct_2(sK3,X4,X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X7))) | ~r1_tarski(k2_relset_1(X4,X5,sK3),k1_relset_1(X5,X7,X6)) | k1_xboole_0 = X5 | k8_funct_2(X4,X5,X7,sK3,X6) = k1_partfun1(X4,X5,X5,X7,sK3,X6)) ) | ~spl6_41),
% 0.22/0.53    inference(avatar_component_clause,[],[f277])).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    spl6_41 | ~spl6_2 | ~spl6_38),
% 0.22/0.53    inference(avatar_split_clause,[],[f266,f262,f75,f277])).
% 0.22/0.53  fof(f262,plain,(
% 0.22/0.53    spl6_38 <=> ! [X1,X3,X0,X2,X4] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | k1_xboole_0 = X1 | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.22/0.53  fof(f266,plain,(
% 0.22/0.53    ( ! [X6,X4,X7,X5] : (~v1_funct_2(sK3,X4,X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X5,X7))) | ~r1_tarski(k2_relset_1(X4,X5,sK3),k1_relset_1(X5,X7,X6)) | k1_xboole_0 = X5 | k8_funct_2(X4,X5,X7,sK3,X6) = k1_partfun1(X4,X5,X5,X7,sK3,X6)) ) | (~spl6_2 | ~spl6_38)),
% 0.22/0.53    inference(resolution,[],[f263,f76])).
% 0.22/0.53  fof(f263,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | k1_xboole_0 = X1 | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)) ) | ~spl6_38),
% 0.22/0.53    inference(avatar_component_clause,[],[f262])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    spl6_38),
% 0.22/0.53    inference(avatar_split_clause,[],[f62,f262])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | k1_xboole_0 = X1 | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    spl6_37),
% 0.22/0.53    inference(avatar_split_clause,[],[f63,f258])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    spl6_36 | ~spl6_8 | ~spl6_23 | ~spl6_34),
% 0.22/0.53    inference(avatar_split_clause,[],[f251,f223,f163,f99,f254])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    spl6_23 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    spl6_34 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    sK1 = k1_relat_1(sK3) | (~spl6_8 | ~spl6_23 | ~spl6_34)),
% 0.22/0.53    inference(subsumption_resolution,[],[f247,f100])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_23 | ~spl6_34)),
% 0.22/0.53    inference(superposition,[],[f224,f164])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_23),
% 0.22/0.53    inference(avatar_component_clause,[],[f163])).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl6_34),
% 0.22/0.53    inference(avatar_component_clause,[],[f223])).
% 0.22/0.53  fof(f241,plain,(
% 0.22/0.53    ~spl6_11 | spl6_24 | ~spl6_35),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f240])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    $false | (~spl6_11 | spl6_24 | ~spl6_35)),
% 0.22/0.53    inference(subsumption_resolution,[],[f235,f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl6_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    spl6_11 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl6_24 | ~spl6_35)),
% 0.22/0.53    inference(backward_demodulation,[],[f170,f227])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | ~spl6_35),
% 0.22/0.53    inference(avatar_component_clause,[],[f226])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl6_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f169])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    spl6_24 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.53  fof(f228,plain,(
% 0.22/0.53    spl6_34 | spl6_35 | ~spl6_6 | ~spl6_8 | ~spl6_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f216,f205,f99,f91,f226,f223])).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    spl6_31 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | (~spl6_6 | ~spl6_8 | ~spl6_31)),
% 0.22/0.53    inference(subsumption_resolution,[],[f214,f100])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_6 | ~spl6_31)),
% 0.22/0.53    inference(resolution,[],[f206,f92])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_31),
% 0.22/0.53    inference(avatar_component_clause,[],[f205])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    spl6_33),
% 0.22/0.53    inference(avatar_split_clause,[],[f50,f219])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    spl6_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f60,f205])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(flattening,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    ~spl6_24 | spl6_3 | ~spl6_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f160,f157,f79,f169])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl6_3 <=> v1_xboole_0(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    spl6_22 <=> ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (spl6_3 | ~spl6_22)),
% 0.22/0.53    inference(resolution,[],[f158,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ~v1_xboole_0(sK2) | spl6_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f79])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl6_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f157])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    spl6_23),
% 0.22/0.53    inference(avatar_split_clause,[],[f54,f163])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    spl6_22 | ~spl6_15 | ~spl6_20),
% 0.22/0.53    inference(avatar_split_clause,[],[f151,f148,f127,f157])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    spl6_15 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl6_20 <=> ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | (~spl6_15 | ~spl6_20)),
% 0.22/0.53    inference(resolution,[],[f149,f128])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl6_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f127])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) ) | ~spl6_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f148])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    spl6_20 | ~spl6_10 | ~spl6_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f146,f135,f107,f148])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl6_10 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    spl6_17 <=> ! [X1,X0] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) ) | (~spl6_10 | ~spl6_17)),
% 0.22/0.53    inference(resolution,[],[f136,f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl6_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f107])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) ) | ~spl6_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f135])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    spl6_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f53,f143])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    spl6_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f49,f139])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    spl6_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f48,f135])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    spl6_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f52,f127])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    spl6_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f47,f119])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ~spl6_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f38,f115])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f14])).
% 0.22/0.53  fof(f14,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    spl6_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f46,f111])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl6_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f45,f107])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl6_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f103])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl6_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f43,f99])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f95])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    spl6_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f42,f91])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ~spl6_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f37,f87])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f83])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    m1_subset_1(sK5,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ~spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f44,f79])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ~v1_xboole_0(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl6_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f75])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    v1_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    spl6_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f71])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    v1_funct_1(sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (12181)------------------------------
% 0.22/0.53  % (12181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12181)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (12181)Memory used [KB]: 10874
% 0.22/0.53  % (12181)Time elapsed: 0.119 s
% 0.22/0.53  % (12181)------------------------------
% 0.22/0.53  % (12181)------------------------------
% 0.22/0.54  % (12171)Success in time 0.169 s
%------------------------------------------------------------------------------
