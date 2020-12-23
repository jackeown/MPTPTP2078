%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 327 expanded)
%              Number of leaves         :   50 ( 144 expanded)
%              Depth                    :   11
%              Number of atoms          :  520 ( 959 expanded)
%              Number of equality atoms :  100 ( 169 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f135,f140,f153,f166,f178,f202,f358,f431,f432,f492,f525,f562,f599,f622,f653,f666,f704,f781,f782,f800,f819,f834,f838,f850,f861,f863,f958,f1108])).

fof(f1108,plain,(
    spl6_111 ),
    inference(avatar_contradiction_clause,[],[f1104])).

fof(f1104,plain,
    ( $false
    | spl6_111 ),
    inference(resolution,[],[f1098,f957])).

fof(f957,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl6_111 ),
    inference(avatar_component_clause,[],[f955])).

fof(f955,plain,
    ( spl6_111
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

% (27066)Refutation not found, incomplete strategy% (27066)------------------------------
% (27066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27066)Termination reason: Refutation not found, incomplete strategy

% (27066)Memory used [KB]: 10618
% (27066)Time elapsed: 0.150 s
% (27066)------------------------------
% (27066)------------------------------
fof(f1098,plain,(
    ! [X3] : v1_funct_2(k1_xboole_0,k1_xboole_0,X3) ),
    inference(superposition,[],[f81,f1037])).

fof(f1037,plain,(
    ! [X1] : k1_xboole_0 = sK5(k1_xboole_0,X1) ),
    inference(resolution,[],[f1035,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1035,plain,(
    ! [X2] : v1_xboole_0(sK5(k1_xboole_0,X2)) ),
    inference(global_subsumption,[],[f53,f1033])).

fof(f1033,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(sK5(k1_xboole_0,X2)) ) ),
    inference(resolution,[],[f419,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f419,plain,(
    ! [X1] : m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f78,f92])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

% (27067)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f78,plain,(
    ! [X0,X1] : m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f81,plain,(
    ! [X0,X1] : v1_funct_2(sK5(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f24])).

fof(f958,plain,
    ( ~ spl6_111
    | ~ spl6_19
    | spl6_99
    | ~ spl6_100 ),
    inference(avatar_split_clause,[],[f953,f847,f831,f199,f955])).

fof(f199,plain,
    ( spl6_19
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

% (27069)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f831,plain,
    ( spl6_99
  <=> v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).

fof(f847,plain,
    ( spl6_100
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f953,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl6_19
    | spl6_99
    | ~ spl6_100 ),
    inference(forward_demodulation,[],[f952,f201])).

fof(f201,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f199])).

fof(f952,plain,
    ( ~ v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl6_99
    | ~ spl6_100 ),
    inference(forward_demodulation,[],[f833,f849])).

fof(f849,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f847])).

fof(f833,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | spl6_99 ),
    inference(avatar_component_clause,[],[f831])).

fof(f863,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k4_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK2
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f861,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | sK1 != k2_relat_1(sK2)
    | k2_funct_1(sK2) != k4_relat_1(sK2)
    | sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f850,plain,
    ( spl6_100
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f841,f403,f847])).

fof(f403,plain,
    ( spl6_49
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f841,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_49 ),
    inference(resolution,[],[f405,f55])).

fof(f405,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f403])).

fof(f838,plain,
    ( spl6_49
    | ~ spl6_9
    | ~ spl6_94 ),
    inference(avatar_split_clause,[],[f836,f797,f137,f403])).

fof(f137,plain,
    ( spl6_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f797,plain,
    ( spl6_94
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f836,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2)
    | ~ spl6_94 ),
    inference(resolution,[],[f799,f59])).

fof(f799,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f797])).

fof(f834,plain,
    ( ~ spl6_99
    | spl6_7
    | ~ spl6_64
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f829,f778,f522,f128,f831])).

fof(f128,plain,
    ( spl6_7
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f522,plain,
    ( spl6_64
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f778,plain,
    ( spl6_92
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f829,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)
    | spl6_7
    | ~ spl6_64
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f828,f524])).

fof(f524,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f522])).

fof(f828,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl6_7
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f130,f780])).

% (27067)Refutation not found, incomplete strategy% (27067)------------------------------
% (27067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27067)Termination reason: Refutation not found, incomplete strategy

% (27067)Memory used [KB]: 10618
% (27067)Time elapsed: 0.150 s
% (27067)------------------------------
% (27067)------------------------------
fof(f780,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f778])).

fof(f130,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f819,plain,
    ( ~ spl6_97
    | spl6_74
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f814,f778,f596,f816])).

fof(f816,plain,
    ( spl6_97
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f596,plain,
    ( spl6_74
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f814,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl6_74
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f788,f92])).

fof(f788,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl6_74
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f598,f780])).

fof(f598,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_74 ),
    inference(avatar_component_clause,[],[f596])).

fof(f800,plain,
    ( spl6_94
    | ~ spl6_3
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f795,f778,f109,f797])).

fof(f109,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f795,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f784,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f784,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_92 ),
    inference(backward_demodulation,[],[f111,f780])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f782,plain,
    ( sK1 != k2_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | k2_funct_1(sK2) != k4_relat_1(sK2)
    | sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f781,plain,
    ( ~ spl6_4
    | spl6_91
    | spl6_92
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f767,f109,f778,f774,f114])).

fof(f114,plain,
    ( spl6_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f774,plain,
    ( spl6_91
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f767,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f90,f111])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f704,plain,
    ( spl6_88
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f699,f109,f99,f701])).

fof(f701,plain,
    ( spl6_88
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f99,plain,
    ( spl6_1
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f699,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f693,f101])).

% (27062)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f101,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f693,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f84,f111])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f666,plain,
    ( spl6_83
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f656,f109,f663])).

fof(f663,plain,
    ( spl6_83
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f656,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f83,f111])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f653,plain,
    ( ~ spl6_42
    | ~ spl6_5
    | spl6_82
    | ~ spl6_2
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f648,f522,f104,f650,f119,f355])).

fof(f355,plain,
    ( spl6_42
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f119,plain,
    ( spl6_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f650,plain,
    ( spl6_82
  <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f104,plain,
    ( spl6_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f648,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_64 ),
    inference(forward_demodulation,[],[f647,f524])).

fof(f647,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f66,f106])).

fof(f106,plain,
    ( v2_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f622,plain,
    ( ~ spl6_42
    | ~ spl6_5
    | spl6_77
    | ~ spl6_2
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f617,f522,f104,f619,f119,f355])).

fof(f619,plain,
    ( spl6_77
  <=> k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f617,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_2
    | ~ spl6_64 ),
    inference(forward_demodulation,[],[f616,f524])).

fof(f616,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f65,f106])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f599,plain,
    ( ~ spl6_74
    | spl6_6
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f574,f522,f124,f596])).

fof(f124,plain,
    ( spl6_6
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f574,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_6
    | ~ spl6_64 ),
    inference(backward_demodulation,[],[f126,f524])).

fof(f126,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f562,plain,
    ( spl6_68
    | ~ spl6_41
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f539,f132,f351,f559])).

fof(f559,plain,
    ( spl6_68
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f351,plain,
    ( spl6_41
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f132,plain,
    ( spl6_8
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f539,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl6_8 ),
    inference(resolution,[],[f61,f133])).

fof(f133,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f525,plain,
    ( spl6_64
    | ~ spl6_42
    | ~ spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f520,f104,f119,f355,f522])).

fof(f520,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f64,f106])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f492,plain,
    ( spl6_59
    | ~ spl6_41
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f463,f132,f351,f489])).

fof(f489,plain,
    ( spl6_59
  <=> v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f463,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl6_8 ),
    inference(resolution,[],[f60,f133])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f432,plain,
    ( spl6_8
    | ~ spl6_42
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f361,f119,f355,f132])).

fof(f361,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f63,f121])).

fof(f121,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f431,plain,
    ( spl6_42
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f426,f109,f355])).

fof(f426,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f82,f111])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f358,plain,
    ( spl6_41
    | ~ spl6_42
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f343,f119,f355,f351])).

fof(f343,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_5 ),
    inference(resolution,[],[f62,f121])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f202,plain,
    ( spl6_19
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f186,f175,f199])).

fof(f175,plain,
    ( spl6_15
  <=> v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f186,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl6_15 ),
    inference(resolution,[],[f177,f55])).

fof(f177,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f178,plain,
    ( spl6_15
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f172,f137,f175])).

fof(f172,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl6_9 ),
    inference(resolution,[],[f57,f139])).

fof(f139,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f137])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

fof(f166,plain,
    ( spl6_13
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f155,f150,f163])).

fof(f163,plain,
    ( spl6_13
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f150,plain,
    ( spl6_11
  <=> v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f155,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_11 ),
    inference(resolution,[],[f152,f55])).

fof(f152,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f153,plain,
    ( spl6_11
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f148,f137,f150])).

fof(f148,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl6_9 ),
    inference(resolution,[],[f56,f139])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f140,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f53,f137])).

fof(f135,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f47,f132,f128,f124])).

fof(f47,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f122,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f48,f119])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f117,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f49,f114])).

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f112,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f50,f109])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f107,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f51,f104])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f102,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f52,f99])).

fof(f52,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:19:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (27056)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (27071)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (27058)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (27063)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (27064)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (27065)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (27080)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (27072)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (27057)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (27059)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (27064)Refutation not found, incomplete strategy% (27064)------------------------------
% 0.22/0.54  % (27064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27064)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27064)Memory used [KB]: 10746
% 0.22/0.54  % (27064)Time elapsed: 0.107 s
% 0.22/0.54  % (27064)------------------------------
% 0.22/0.54  % (27064)------------------------------
% 0.22/0.54  % (27061)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (27082)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (27084)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (27079)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (27060)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (27081)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (27060)Refutation not found, incomplete strategy% (27060)------------------------------
% 0.22/0.54  % (27060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27060)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27060)Memory used [KB]: 6396
% 0.22/0.54  % (27060)Time elapsed: 0.127 s
% 0.22/0.54  % (27060)------------------------------
% 0.22/0.54  % (27060)------------------------------
% 0.22/0.54  % (27078)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (27083)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (27058)Refutation not found, incomplete strategy% (27058)------------------------------
% 0.22/0.55  % (27058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27058)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27058)Memory used [KB]: 11001
% 0.22/0.55  % (27058)Time elapsed: 0.129 s
% 0.22/0.55  % (27058)------------------------------
% 0.22/0.55  % (27058)------------------------------
% 0.22/0.55  % (27077)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (27076)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (27078)Refutation not found, incomplete strategy% (27078)------------------------------
% 0.22/0.55  % (27078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27078)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27078)Memory used [KB]: 10874
% 0.22/0.55  % (27078)Time elapsed: 0.100 s
% 0.22/0.55  % (27078)------------------------------
% 0.22/0.55  % (27078)------------------------------
% 0.22/0.55  % (27074)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (27085)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (27075)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (27070)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (27073)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (27068)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (27073)Refutation not found, incomplete strategy% (27073)------------------------------
% 0.22/0.55  % (27073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27073)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27073)Memory used [KB]: 10618
% 0.22/0.55  % (27073)Time elapsed: 0.139 s
% 0.22/0.55  % (27073)------------------------------
% 0.22/0.55  % (27073)------------------------------
% 0.22/0.55  % (27066)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (27072)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f1113,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f135,f140,f153,f166,f178,f202,f358,f431,f432,f492,f525,f562,f599,f622,f653,f666,f704,f781,f782,f800,f819,f834,f838,f850,f861,f863,f958,f1108])).
% 0.22/0.56  fof(f1108,plain,(
% 0.22/0.56    spl6_111),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f1104])).
% 0.22/0.56  fof(f1104,plain,(
% 0.22/0.56    $false | spl6_111),
% 0.22/0.56    inference(resolution,[],[f1098,f957])).
% 0.22/0.56  fof(f957,plain,(
% 0.22/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | spl6_111),
% 0.22/0.56    inference(avatar_component_clause,[],[f955])).
% 0.22/0.56  fof(f955,plain,(
% 0.22/0.56    spl6_111 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).
% 0.22/0.56  % (27066)Refutation not found, incomplete strategy% (27066)------------------------------
% 0.22/0.56  % (27066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27066)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (27066)Memory used [KB]: 10618
% 0.22/0.56  % (27066)Time elapsed: 0.150 s
% 0.22/0.56  % (27066)------------------------------
% 0.22/0.56  % (27066)------------------------------
% 0.22/0.56  fof(f1098,plain,(
% 0.22/0.56    ( ! [X3] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X3)) )),
% 0.22/0.56    inference(superposition,[],[f81,f1037])).
% 0.22/0.56  fof(f1037,plain,(
% 0.22/0.56    ( ! [X1] : (k1_xboole_0 = sK5(k1_xboole_0,X1)) )),
% 0.22/0.56    inference(resolution,[],[f1035,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.56  fof(f1035,plain,(
% 0.22/0.56    ( ! [X2] : (v1_xboole_0(sK5(k1_xboole_0,X2))) )),
% 0.22/0.56    inference(global_subsumption,[],[f53,f1033])).
% 0.22/0.56  fof(f1033,plain,(
% 0.22/0.56    ( ! [X2] : (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK5(k1_xboole_0,X2))) )),
% 0.22/0.56    inference(resolution,[],[f419,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.56  fof(f419,plain,(
% 0.22/0.56    ( ! [X1] : (m1_subset_1(sK5(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) )),
% 0.22/0.56    inference(superposition,[],[f78,f92])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.56    inference(equality_resolution,[],[f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  % (27067)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f19])).
% 0.22/0.56  fof(f19,axiom,(
% 0.22/0.56    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_funct_2(sK5(X0,X1),X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f958,plain,(
% 0.22/0.56    ~spl6_111 | ~spl6_19 | spl6_99 | ~spl6_100),
% 0.22/0.56    inference(avatar_split_clause,[],[f953,f847,f831,f199,f955])).
% 0.22/0.56  fof(f199,plain,(
% 0.22/0.56    spl6_19 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.56  % (27069)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  fof(f831,plain,(
% 0.22/0.56    spl6_99 <=> v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_99])])).
% 0.22/0.56  fof(f847,plain,(
% 0.22/0.56    spl6_100 <=> k1_xboole_0 = sK2),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).
% 0.22/0.56  fof(f953,plain,(
% 0.22/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (~spl6_19 | spl6_99 | ~spl6_100)),
% 0.22/0.56    inference(forward_demodulation,[],[f952,f201])).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl6_19),
% 0.22/0.56    inference(avatar_component_clause,[],[f199])).
% 0.22/0.56  fof(f952,plain,(
% 0.22/0.56    ~v1_funct_2(k4_relat_1(k1_xboole_0),k1_xboole_0,sK0) | (spl6_99 | ~spl6_100)),
% 0.22/0.56    inference(forward_demodulation,[],[f833,f849])).
% 0.22/0.56  fof(f849,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | ~spl6_100),
% 0.22/0.56    inference(avatar_component_clause,[],[f847])).
% 0.22/0.56  fof(f833,plain,(
% 0.22/0.56    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | spl6_99),
% 0.22/0.56    inference(avatar_component_clause,[],[f831])).
% 0.22/0.56  fof(f863,plain,(
% 0.22/0.56    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k4_relat_1(k1_xboole_0) | k1_xboole_0 != sK2 | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f861,plain,(
% 0.22/0.56    k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | sK1 != k2_relat_1(sK2) | k2_funct_1(sK2) != k4_relat_1(sK2) | sK0 != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f850,plain,(
% 0.22/0.56    spl6_100 | ~spl6_49),
% 0.22/0.56    inference(avatar_split_clause,[],[f841,f403,f847])).
% 0.22/0.56  fof(f403,plain,(
% 0.22/0.56    spl6_49 <=> v1_xboole_0(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.22/0.56  fof(f841,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | ~spl6_49),
% 0.22/0.56    inference(resolution,[],[f405,f55])).
% 0.22/0.56  fof(f405,plain,(
% 0.22/0.56    v1_xboole_0(sK2) | ~spl6_49),
% 0.22/0.56    inference(avatar_component_clause,[],[f403])).
% 0.22/0.56  fof(f838,plain,(
% 0.22/0.56    spl6_49 | ~spl6_9 | ~spl6_94),
% 0.22/0.56    inference(avatar_split_clause,[],[f836,f797,f137,f403])).
% 0.22/0.56  fof(f137,plain,(
% 0.22/0.56    spl6_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.56  fof(f797,plain,(
% 0.22/0.56    spl6_94 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 0.22/0.56  fof(f836,plain,(
% 0.22/0.56    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2) | ~spl6_94),
% 0.22/0.56    inference(resolution,[],[f799,f59])).
% 0.22/0.56  fof(f799,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_94),
% 0.22/0.56    inference(avatar_component_clause,[],[f797])).
% 0.22/0.56  fof(f834,plain,(
% 0.22/0.56    ~spl6_99 | spl6_7 | ~spl6_64 | ~spl6_92),
% 0.22/0.56    inference(avatar_split_clause,[],[f829,f778,f522,f128,f831])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    spl6_7 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.56  fof(f522,plain,(
% 0.22/0.56    spl6_64 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 0.22/0.56  fof(f778,plain,(
% 0.22/0.56    spl6_92 <=> k1_xboole_0 = sK1),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).
% 0.22/0.56  fof(f829,plain,(
% 0.22/0.56    ~v1_funct_2(k4_relat_1(sK2),k1_xboole_0,sK0) | (spl6_7 | ~spl6_64 | ~spl6_92)),
% 0.22/0.56    inference(forward_demodulation,[],[f828,f524])).
% 0.22/0.56  fof(f524,plain,(
% 0.22/0.56    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl6_64),
% 0.22/0.56    inference(avatar_component_clause,[],[f522])).
% 0.22/0.56  fof(f828,plain,(
% 0.22/0.56    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl6_7 | ~spl6_92)),
% 0.22/0.56    inference(forward_demodulation,[],[f130,f780])).
% 0.22/0.56  % (27067)Refutation not found, incomplete strategy% (27067)------------------------------
% 0.22/0.56  % (27067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27067)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (27067)Memory used [KB]: 10618
% 0.22/0.56  % (27067)Time elapsed: 0.150 s
% 0.22/0.56  % (27067)------------------------------
% 0.22/0.56  % (27067)------------------------------
% 0.22/0.56  fof(f780,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | ~spl6_92),
% 0.22/0.56    inference(avatar_component_clause,[],[f778])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl6_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f128])).
% 0.22/0.56  fof(f819,plain,(
% 0.22/0.56    ~spl6_97 | spl6_74 | ~spl6_92),
% 0.22/0.56    inference(avatar_split_clause,[],[f814,f778,f596,f816])).
% 0.22/0.56  fof(f816,plain,(
% 0.22/0.56    spl6_97 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).
% 0.22/0.56  fof(f596,plain,(
% 0.22/0.56    spl6_74 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 0.22/0.56  fof(f814,plain,(
% 0.22/0.56    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl6_74 | ~spl6_92)),
% 0.22/0.56    inference(forward_demodulation,[],[f788,f92])).
% 0.22/0.56  fof(f788,plain,(
% 0.22/0.56    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl6_74 | ~spl6_92)),
% 0.22/0.56    inference(backward_demodulation,[],[f598,f780])).
% 0.22/0.56  fof(f598,plain,(
% 0.22/0.56    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_74),
% 0.22/0.56    inference(avatar_component_clause,[],[f596])).
% 0.22/0.56  fof(f800,plain,(
% 0.22/0.56    spl6_94 | ~spl6_3 | ~spl6_92),
% 0.22/0.56    inference(avatar_split_clause,[],[f795,f778,f109,f797])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.56  fof(f795,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | ~spl6_92)),
% 0.22/0.56    inference(forward_demodulation,[],[f784,f91])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f784,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_3 | ~spl6_92)),
% 0.22/0.56    inference(backward_demodulation,[],[f111,f780])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f109])).
% 0.22/0.56  fof(f782,plain,(
% 0.22/0.56    sK1 != k2_relat_1(sK2) | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | k2_funct_1(sK2) != k4_relat_1(sK2) | sK0 != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f781,plain,(
% 0.22/0.56    ~spl6_4 | spl6_91 | spl6_92 | ~spl6_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f767,f109,f778,f774,f114])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    spl6_4 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.56  fof(f774,plain,(
% 0.22/0.56    spl6_91 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 0.22/0.56  fof(f767,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl6_3),
% 0.22/0.56    inference(resolution,[],[f90,f111])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.56  fof(f704,plain,(
% 0.22/0.56    spl6_88 | ~spl6_1 | ~spl6_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f699,f109,f99,f701])).
% 0.22/0.56  fof(f701,plain,(
% 0.22/0.56    spl6_88 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    spl6_1 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.56  fof(f699,plain,(
% 0.22/0.56    sK1 = k2_relat_1(sK2) | (~spl6_1 | ~spl6_3)),
% 0.22/0.56    inference(forward_demodulation,[],[f693,f101])).
% 0.22/0.56  % (27062)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl6_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f99])).
% 0.22/0.56  fof(f693,plain,(
% 0.22/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl6_3),
% 0.22/0.56    inference(resolution,[],[f84,f111])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.56  fof(f666,plain,(
% 0.22/0.56    spl6_83 | ~spl6_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f656,f109,f663])).
% 0.22/0.56  fof(f663,plain,(
% 0.22/0.56    spl6_83 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 0.22/0.56  fof(f656,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl6_3),
% 0.22/0.56    inference(resolution,[],[f83,f111])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f653,plain,(
% 0.22/0.56    ~spl6_42 | ~spl6_5 | spl6_82 | ~spl6_2 | ~spl6_64),
% 0.22/0.56    inference(avatar_split_clause,[],[f648,f522,f104,f650,f119,f355])).
% 0.22/0.56  fof(f355,plain,(
% 0.22/0.56    spl6_42 <=> v1_relat_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    spl6_5 <=> v1_funct_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.56  fof(f650,plain,(
% 0.22/0.56    spl6_82 <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    spl6_2 <=> v2_funct_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.56  fof(f648,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_2 | ~spl6_64)),
% 0.22/0.56    inference(forward_demodulation,[],[f647,f524])).
% 0.22/0.56  fof(f647,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~spl6_2),
% 0.22/0.56    inference(resolution,[],[f66,f106])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    v2_funct_1(sK2) | ~spl6_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f104])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.56  fof(f622,plain,(
% 0.22/0.56    ~spl6_42 | ~spl6_5 | spl6_77 | ~spl6_2 | ~spl6_64),
% 0.22/0.56    inference(avatar_split_clause,[],[f617,f522,f104,f619,f119,f355])).
% 0.22/0.56  fof(f619,plain,(
% 0.22/0.56    spl6_77 <=> k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 0.22/0.56  fof(f617,plain,(
% 0.22/0.56    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_2 | ~spl6_64)),
% 0.22/0.56    inference(forward_demodulation,[],[f616,f524])).
% 0.22/0.56  fof(f616,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) | ~spl6_2),
% 0.22/0.56    inference(resolution,[],[f65,f106])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f599,plain,(
% 0.22/0.56    ~spl6_74 | spl6_6 | ~spl6_64),
% 0.22/0.56    inference(avatar_split_clause,[],[f574,f522,f124,f596])).
% 0.22/0.56  fof(f124,plain,(
% 0.22/0.56    spl6_6 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.56  fof(f574,plain,(
% 0.22/0.56    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl6_6 | ~spl6_64)),
% 0.22/0.56    inference(backward_demodulation,[],[f126,f524])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f124])).
% 0.22/0.56  fof(f562,plain,(
% 0.22/0.56    spl6_68 | ~spl6_41 | ~spl6_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f539,f132,f351,f559])).
% 0.22/0.56  fof(f559,plain,(
% 0.22/0.56    spl6_68 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 0.22/0.56  fof(f351,plain,(
% 0.22/0.56    spl6_41 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.22/0.56  fof(f132,plain,(
% 0.22/0.56    spl6_8 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.56  fof(f539,plain,(
% 0.22/0.56    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl6_8),
% 0.22/0.56    inference(resolution,[],[f61,f133])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    v1_funct_1(k2_funct_1(sK2)) | ~spl6_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f132])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.56  fof(f525,plain,(
% 0.22/0.56    spl6_64 | ~spl6_42 | ~spl6_5 | ~spl6_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f520,f104,f119,f355,f522])).
% 0.22/0.56  fof(f520,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl6_2),
% 0.22/0.56    inference(resolution,[],[f64,f106])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.22/0.56  fof(f492,plain,(
% 0.22/0.56    spl6_59 | ~spl6_41 | ~spl6_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f463,f132,f351,f489])).
% 0.22/0.56  fof(f489,plain,(
% 0.22/0.56    spl6_59 <=> v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.22/0.56  fof(f463,plain,(
% 0.22/0.56    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl6_8),
% 0.22/0.56    inference(resolution,[],[f60,f133])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f432,plain,(
% 0.22/0.56    spl6_8 | ~spl6_42 | ~spl6_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f361,f119,f355,f132])).
% 0.22/0.56  fof(f361,plain,(
% 0.22/0.56    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl6_5),
% 0.22/0.56    inference(resolution,[],[f63,f121])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    v1_funct_1(sK2) | ~spl6_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f119])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.56  fof(f431,plain,(
% 0.22/0.56    spl6_42 | ~spl6_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f426,f109,f355])).
% 0.22/0.56  fof(f426,plain,(
% 0.22/0.56    v1_relat_1(sK2) | ~spl6_3),
% 0.22/0.56    inference(resolution,[],[f82,f111])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.56  fof(f358,plain,(
% 0.22/0.56    spl6_41 | ~spl6_42 | ~spl6_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f343,f119,f355,f351])).
% 0.22/0.56  fof(f343,plain,(
% 0.22/0.56    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl6_5),
% 0.22/0.56    inference(resolution,[],[f62,f121])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f202,plain,(
% 0.22/0.56    spl6_19 | ~spl6_15),
% 0.22/0.56    inference(avatar_split_clause,[],[f186,f175,f199])).
% 0.22/0.56  fof(f175,plain,(
% 0.22/0.56    spl6_15 <=> v1_xboole_0(k4_relat_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl6_15),
% 0.22/0.56    inference(resolution,[],[f177,f55])).
% 0.22/0.56  fof(f177,plain,(
% 0.22/0.56    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl6_15),
% 0.22/0.56    inference(avatar_component_clause,[],[f175])).
% 0.22/0.56  fof(f178,plain,(
% 0.22/0.56    spl6_15 | ~spl6_9),
% 0.22/0.56    inference(avatar_split_clause,[],[f172,f137,f175])).
% 0.22/0.56  fof(f172,plain,(
% 0.22/0.56    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl6_9),
% 0.22/0.56    inference(resolution,[],[f57,f139])).
% 0.22/0.56  fof(f139,plain,(
% 0.22/0.56    v1_xboole_0(k1_xboole_0) | ~spl6_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f137])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k4_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).
% 0.22/0.56  fof(f166,plain,(
% 0.22/0.56    spl6_13 | ~spl6_11),
% 0.22/0.56    inference(avatar_split_clause,[],[f155,f150,f163])).
% 0.22/0.56  fof(f163,plain,(
% 0.22/0.56    spl6_13 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.56  fof(f150,plain,(
% 0.22/0.56    spl6_11 <=> v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.56  fof(f155,plain,(
% 0.22/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl6_11),
% 0.22/0.56    inference(resolution,[],[f152,f55])).
% 0.22/0.56  fof(f152,plain,(
% 0.22/0.56    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl6_11),
% 0.22/0.56    inference(avatar_component_clause,[],[f150])).
% 0.22/0.56  fof(f153,plain,(
% 0.22/0.56    spl6_11 | ~spl6_9),
% 0.22/0.56    inference(avatar_split_clause,[],[f148,f137,f150])).
% 0.22/0.56  fof(f148,plain,(
% 0.22/0.56    v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~spl6_9),
% 0.22/0.56    inference(resolution,[],[f56,f139])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.22/0.56  fof(f140,plain,(
% 0.22/0.56    spl6_9),
% 0.22/0.56    inference(avatar_split_clause,[],[f53,f137])).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    ~spl6_6 | ~spl6_7 | ~spl6_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f47,f132,f128,f124])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.56    inference(negated_conjecture,[],[f21])).
% 0.22/0.56  fof(f21,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    spl6_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f48,f119])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    v1_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    spl6_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f49,f114])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    spl6_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f50,f109])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    spl6_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f51,f104])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    v2_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    spl6_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f52,f99])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (27072)------------------------------
% 0.22/0.56  % (27072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27072)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (27072)Memory used [KB]: 11385
% 0.22/0.56  % (27072)Time elapsed: 0.135 s
% 0.22/0.56  % (27072)------------------------------
% 0.22/0.56  % (27072)------------------------------
% 0.22/0.57  % (27055)Success in time 0.202 s
%------------------------------------------------------------------------------
