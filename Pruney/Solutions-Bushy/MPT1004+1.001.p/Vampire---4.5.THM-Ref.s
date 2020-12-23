%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1004+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:03 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 274 expanded)
%              Number of leaves         :   37 ( 120 expanded)
%              Depth                    :   10
%              Number of atoms          :  488 (1134 expanded)
%              Number of equality atoms :   94 ( 253 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f532,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f80,f84,f88,f92,f100,f119,f168,f180,f232,f311,f340,f361,f370,f383,f390,f393,f398,f402,f461,f530,f531])).

fof(f531,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK5)
    | k1_xboole_0 != sK1
    | sK1 = k1_relset_1(sK1,sK2,sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f530,plain,
    ( spl6_66
    | ~ spl6_58
    | ~ spl6_2
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f525,f230,f71,f459,f527])).

fof(f527,plain,
    ( spl6_66
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f459,plain,
    ( spl6_58
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f71,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f230,plain,
    ( spl6_26
  <=> v1_funct_2(sK5,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f525,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK5)
    | ~ spl6_2
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f524,f164])).

fof(f164,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f524,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl6_2
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f521,f164])).

fof(f521,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl6_26 ),
    inference(resolution,[],[f231,f65])).

fof(f65,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f231,plain,
    ( v1_funct_2(sK5,k1_xboole_0,sK2)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f230])).

fof(f461,plain,
    ( spl6_58
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f457,f78,f74,f71,f459])).

fof(f74,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f78,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f457,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f435,f75])).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f435,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(superposition,[],[f79,f164])).

fof(f79,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f402,plain,
    ( ~ spl6_7
    | spl6_53 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | ~ spl6_7
    | spl6_53 ),
    inference(subsumption_resolution,[],[f91,f399])).

fof(f399,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | spl6_53 ),
    inference(resolution,[],[f397,f108])).

% (9269)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f49,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f397,plain,
    ( ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1))
    | spl6_53 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl6_53
  <=> m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f91,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f398,plain,
    ( ~ spl6_53
    | spl6_51 ),
    inference(avatar_split_clause,[],[f394,f381,f396])).

fof(f381,plain,
    ( spl6_51
  <=> r1_tarski(k2_relat_1(sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f394,plain,
    ( ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK1))
    | spl6_51 ),
    inference(resolution,[],[f382,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f382,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK1)
    | spl6_51 ),
    inference(avatar_component_clause,[],[f381])).

fof(f393,plain,
    ( ~ spl6_4
    | spl6_50 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | ~ spl6_4
    | spl6_50 ),
    inference(subsumption_resolution,[],[f79,f391])).

fof(f391,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_50 ),
    inference(resolution,[],[f379,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f379,plain,
    ( ~ v1_relat_1(sK5)
    | spl6_50 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl6_50
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

% (9256)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f390,plain,
    ( ~ spl6_7
    | spl6_49 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | ~ spl6_7
    | spl6_49 ),
    inference(subsumption_resolution,[],[f91,f388])).

fof(f388,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_49 ),
    inference(resolution,[],[f376,f46])).

fof(f376,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_49 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl6_49
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f383,plain,
    ( ~ spl6_49
    | ~ spl6_50
    | ~ spl6_51
    | ~ spl6_19
    | spl6_48 ),
    inference(avatar_split_clause,[],[f373,f368,f177,f381,f378,f375])).

fof(f177,plain,
    ( spl6_19
  <=> sK1 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f368,plain,
    ( spl6_48
  <=> r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f373,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | ~ spl6_19
    | spl6_48 ),
    inference(forward_demodulation,[],[f371,f178])).

fof(f178,plain,
    ( sK1 = k1_relat_1(sK5)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f371,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK4)
    | spl6_48 ),
    inference(resolution,[],[f369,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0)))
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(k5_relat_1(X1,X2),k9_relat_1(X2,X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_1)).

fof(f369,plain,
    ( ~ r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3)))
    | spl6_48 ),
    inference(avatar_component_clause,[],[f368])).

fof(f370,plain,
    ( ~ spl6_48
    | spl6_44
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f366,f359,f338,f368])).

fof(f338,plain,
    ( spl6_44
  <=> r1_tarski(k10_relat_1(sK4,sK3),k8_relset_1(sK0,sK2,k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f359,plain,
    ( spl6_47
  <=> m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f366,plain,
    ( ~ r1_tarski(k10_relat_1(sK4,sK3),k10_relat_1(k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3)))
    | spl6_44
    | ~ spl6_47 ),
    inference(superposition,[],[f339,f364])).

fof(f364,plain,
    ( ! [X0] : k8_relset_1(sK0,sK2,k5_relat_1(sK4,sK5),X0) = k10_relat_1(k5_relat_1(sK4,sK5),X0)
    | ~ spl6_47 ),
    inference(resolution,[],[f360,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f360,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f359])).

fof(f339,plain,
    ( ~ r1_tarski(k10_relat_1(sK4,sK3),k8_relset_1(sK0,sK2,k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3)))
    | spl6_44 ),
    inference(avatar_component_clause,[],[f338])).

fof(f361,plain,
    ( ~ spl6_9
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_4
    | spl6_47
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f352,f309,f359,f78,f86,f90,f98])).

fof(f98,plain,
    ( spl6_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f86,plain,
    ( spl6_6
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f309,plain,
    ( spl6_40
  <=> k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f352,plain,
    ( m1_subset_1(k5_relat_1(sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ spl6_40 ),
    inference(superposition,[],[f60,f310])).

fof(f310,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f309])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f340,plain,
    ( ~ spl6_44
    | ~ spl6_7
    | spl6_12
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f336,f309,f117,f90,f338])).

fof(f117,plain,
    ( spl6_12
  <=> r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k9_relat_1(sK5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f336,plain,
    ( ~ r1_tarski(k10_relat_1(sK4,sK3),k8_relset_1(sK0,sK2,k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3)))
    | ~ spl6_7
    | spl6_12
    | ~ spl6_40 ),
    inference(forward_demodulation,[],[f315,f123])).

fof(f123,plain,
    ( ! [X1] : k8_relset_1(sK0,sK1,sK4,X1) = k10_relat_1(sK4,X1)
    | ~ spl6_7 ),
    inference(resolution,[],[f57,f91])).

fof(f315,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k5_relat_1(sK4,sK5),k9_relat_1(sK5,sK3)))
    | spl6_12
    | ~ spl6_40 ),
    inference(superposition,[],[f118,f310])).

fof(f118,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k9_relat_1(sK5,sK3)))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f311,plain,
    ( spl6_40
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f306,f98,f90,f86,f78,f309])).

fof(f306,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5) = k5_relat_1(sK4,sK5)
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f288,f91])).

fof(f288,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_partfun1(X2,X3,sK1,sK2,sK4,sK5) = k5_relat_1(sK4,sK5) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_9 ),
    inference(resolution,[],[f285,f99])).

% (9274)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f99,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f285,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_partfun1(X0,X1,sK1,sK2,X2,sK5) = k5_relat_1(X2,sK5) )
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(resolution,[],[f282,f79])).

fof(f282,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_partfun1(X2,X3,X0,X1,X4,sK5) = k5_relat_1(X4,sK5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X4) )
    | ~ spl6_6 ),
    inference(resolution,[],[f58,f87])).

fof(f87,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f232,plain,
    ( spl6_26
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f208,f82,f74,f230])).

fof(f82,plain,
    ( spl6_5
  <=> v1_funct_2(sK5,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f208,plain,
    ( v1_funct_2(sK5,k1_xboole_0,sK2)
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(superposition,[],[f83,f75])).

fof(f83,plain,
    ( v1_funct_2(sK5,sK1,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f180,plain,
    ( ~ spl6_4
    | spl6_19
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f175,f166,f177,f78])).

fof(f166,plain,
    ( spl6_17
  <=> sK1 = k1_relset_1(sK1,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f175,plain,
    ( sK1 = k1_relat_1(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_17 ),
    inference(superposition,[],[f48,f167])).

fof(f167,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK5)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f166])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f168,plain,
    ( ~ spl6_4
    | spl6_2
    | spl6_17
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f160,f82,f166,f71,f78])).

fof(f160,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK5)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_5 ),
    inference(resolution,[],[f50,f83])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f119,plain,
    ( ~ spl6_4
    | ~ spl6_12
    | spl6_1 ),
    inference(avatar_split_clause,[],[f110,f67,f117,f78])).

fof(f67,plain,
    ( spl6_1
  <=> r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f110,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k9_relat_1(sK5,sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_1 ),
    inference(superposition,[],[f68,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f68,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f100,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f35,f98])).

fof(f35,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK5,sK1,sK2)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK4,sK0,sK1)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f15,f31,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5] :
            ( ~ r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3)))
            & ( k1_xboole_0 = X1
              | k1_xboole_0 != X2 )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X5,X1,X2)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,X5),k7_relset_1(sK1,sK2,X5,sK3)))
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X5,sK1,sK2)
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK4,sK0,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

% (9272)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (9256)Refutation not found, incomplete strategy% (9256)------------------------------
% (9256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f31,plain,
    ( ? [X5] :
        ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,X5),k7_relset_1(sK1,sK2,X5,sK3)))
        & ( k1_xboole_0 = sK1
          | k1_xboole_0 != sK2 )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X5,sK1,sK2)
        & v1_funct_1(X5) )
   => ( ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3)))
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK5,sK1,sK2)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

% (9256)Termination reason: Refutation not found, incomplete strategy

% (9256)Memory used [KB]: 10618
% (9256)Time elapsed: 0.079 s
% (9256)------------------------------
% (9256)------------------------------
fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ~ r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3)))
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X5,X1,X2)
          & v1_funct_1(X5) )
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ~ r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3)))
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X5,X1,X2)
          & v1_funct_1(X5) )
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
       => ! [X5] :
            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X5,X1,X2)
              & v1_funct_1(X5) )
           => ( ( k1_xboole_0 = X2
               => k1_xboole_0 = X1 )
             => r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
     => ! [X5] :
          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X5,X1,X2)
            & v1_funct_1(X5) )
         => ( ( k1_xboole_0 = X2
             => k1_xboole_0 = X1 )
           => r1_tarski(k8_relset_1(X0,X1,X4,X3),k8_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X4,X5),k7_relset_1(X1,X2,X5,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_2)).

fof(f92,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f37,f90])).

% (9263)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (9271)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f37,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f38,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    v1_funct_2(sK5,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,
    ( ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f41,f74,f71])).

fof(f41,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f69,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f42,f67])).

fof(f42,plain,(
    ~ r1_tarski(k8_relset_1(sK0,sK1,sK4,sK3),k8_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK4,sK5),k7_relset_1(sK1,sK2,sK5,sK3))) ),
    inference(cnf_transformation,[],[f32])).

%------------------------------------------------------------------------------
