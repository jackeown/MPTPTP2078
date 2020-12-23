%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 511 expanded)
%              Number of leaves         :   62 ( 241 expanded)
%              Depth                    :   10
%              Number of atoms          :  875 (2173 expanded)
%              Number of equality atoms :  178 ( 556 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f583,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f93,f97,f101,f105,f109,f113,f117,f121,f128,f132,f146,f156,f175,f180,f184,f214,f230,f245,f249,f255,f272,f278,f287,f289,f302,f309,f318,f367,f396,f414,f465,f480,f498,f503,f514,f522,f545,f554,f569,f581,f582])).

fof(f582,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f581,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

% (10492)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f569,plain,
    ( ~ spl3_44
    | spl3_67
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_66 ),
    inference(avatar_split_clause,[],[f565,f552,f299,f216,f149,f134,f567,f360])).

fof(f360,plain,
    ( spl3_44
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f567,plain,
    ( spl3_67
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f134,plain,
    ( spl3_13
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f149,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f216,plain,
    ( spl3_24
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f299,plain,
    ( spl3_35
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f552,plain,
    ( spl3_66
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f565,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_66 ),
    inference(trivial_inequality_removal,[],[f564])).

fof(f564,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f563,f135])).

fof(f135,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f563,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f562,f300])).

fof(f300,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f299])).

fof(f562,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f561,f217])).

fof(f217,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f216])).

% (10509)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f561,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f560,f300])).

fof(f560,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_66 ),
    inference(forward_demodulation,[],[f557,f217])).

fof(f557,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_66 ),
    inference(resolution,[],[f553,f150])).

fof(f150,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f553,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f552])).

fof(f554,plain,
    ( ~ spl3_7
    | spl3_66
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f549,f91,f552,f107])).

fof(f107,plain,
    ( spl3_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f91,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f549,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f81,f92])).

fof(f92,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f545,plain,
    ( spl3_64
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f544,f519,f541])).

fof(f541,plain,
    ( spl3_64
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f519,plain,
    ( spl3_59
  <=> k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f544,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f528,f58])).

fof(f58,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f528,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k6_relat_1(k1_relat_1(sK2)))
    | ~ spl3_59 ),
    inference(superposition,[],[f58,f520])).

fof(f520,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f519])).

fof(f522,plain,
    ( ~ spl3_17
    | ~ spl3_7
    | ~ spl3_3
    | spl3_59
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f517,f512,f519,f91,f107,f169])).

fof(f169,plain,
    ( spl3_17
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f512,plain,
    ( spl3_58
  <=> k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f517,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_58 ),
    inference(superposition,[],[f68,f513])).

fof(f513,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f512])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f514,plain,
    ( ~ spl3_17
    | ~ spl3_7
    | spl3_58
    | ~ spl3_3
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f510,f173,f91,f512,f107,f169])).

fof(f173,plain,
    ( spl3_18
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f510,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f508,f174])).

fof(f174,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f508,plain,
    ( k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f310,f92])).

fof(f310,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0)) = k6_relat_1(k2_relat_1(k2_funct_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f66,f65,f304])).

fof(f304,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0)) = k6_relat_1(k2_relat_1(k2_funct_1(X0)))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f69,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f66,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f503,plain,
    ( spl3_57
    | ~ spl3_50
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f499,f478,f392,f501])).

fof(f501,plain,
    ( spl3_57
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f392,plain,
    ( spl3_50
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f478,plain,
    ( spl3_55
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f499,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_50
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f493,f393])).

fof(f393,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f392])).

fof(f493,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_55 ),
    inference(resolution,[],[f479,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f479,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f478])).

fof(f498,plain,
    ( spl3_56
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f492,f478,f496])).

fof(f496,plain,
    ( spl3_56
  <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f492,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_55 ),
    inference(resolution,[],[f479,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f480,plain,
    ( ~ spl3_44
    | spl3_55
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f475,f463,f299,f216,f149,f134,f478,f360])).

fof(f463,plain,
    ( spl3_54
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f475,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f474,f217])).

fof(f474,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f473,f300])).

fof(f473,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_54 ),
    inference(trivial_inequality_removal,[],[f472])).

fof(f472,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f471,f135])).

fof(f471,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_35
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f470,f300])).

fof(f470,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f467,f217])).

fof(f467,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_15
    | ~ spl3_54 ),
    inference(resolution,[],[f464,f150])).

fof(f464,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f463])).

fof(f465,plain,
    ( ~ spl3_7
    | spl3_54
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f460,f91,f463,f107])).

fof(f460,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f80,f92])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f414,plain,
    ( ~ spl3_30
    | spl3_31
    | ~ spl3_29
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f408,f316,f243,f253,f247])).

fof(f247,plain,
    ( spl3_30
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f253,plain,
    ( spl3_31
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f243,plain,
    ( spl3_29
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f316,plain,
    ( spl3_38
  <=> ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f408,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_29
    | ~ spl3_38 ),
    inference(resolution,[],[f317,f244])).

fof(f244,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f243])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
        | v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,k2_struct_0(sK0),X0) )
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f316])).

fof(f396,plain,
    ( spl3_50
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f395,f307,f392])).

fof(f307,plain,
    ( spl3_36
  <=> k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f395,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f379,f58])).

fof(f379,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ spl3_36 ),
    inference(superposition,[],[f58,f308])).

fof(f308,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f307])).

fof(f367,plain,
    ( spl3_44
    | ~ spl3_30
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f345,f299,f247,f360])).

% (10508)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f345,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_30
    | ~ spl3_35 ),
    inference(superposition,[],[f248,f300])).

fof(f248,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f247])).

fof(f318,plain,
    ( ~ spl3_7
    | spl3_38
    | spl3_34 ),
    inference(avatar_split_clause,[],[f314,f296,f316,f107])).

fof(f296,plain,
    ( spl3_34
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),X0)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
        | v1_xboole_0(X0) )
    | spl3_34 ),
    inference(resolution,[],[f71,f297])).

fof(f297,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f296])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f309,plain,
    ( ~ spl3_17
    | ~ spl3_7
    | spl3_36
    | ~ spl3_3
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f305,f270,f91,f307,f107,f169])).

fof(f270,plain,
    ( spl3_32
  <=> k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f305,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f303,f271])).

fof(f271,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f270])).

fof(f303,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f69,f92])).

fof(f302,plain,
    ( ~ spl3_34
    | spl3_35
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f294,f243,f299,f296])).

fof(f294,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_29 ),
    inference(resolution,[],[f204,f244])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(X0) = X1
      | ~ v1_partfun1(X0,X1) ) ),
    inference(global_subsumption,[],[f74,f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f72,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f289,plain,
    ( ~ spl3_17
    | ~ spl3_7
    | ~ spl3_3
    | spl3_21 ),
    inference(avatar_split_clause,[],[f288,f197,f91,f107,f169])).

fof(f197,plain,
    ( spl3_21
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f288,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_21 ),
    inference(resolution,[],[f198,f64])).

fof(f198,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f197])).

fof(f287,plain,
    ( ~ spl3_17
    | ~ spl3_7
    | spl3_20 ),
    inference(avatar_split_clause,[],[f281,f194,f107,f169])).

fof(f194,plain,
    ( spl3_20
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f281,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_20 ),
    inference(resolution,[],[f195,f66])).

fof(f195,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f194])).

fof(f278,plain,
    ( ~ spl3_17
    | ~ spl3_7
    | spl3_19 ),
    inference(avatar_split_clause,[],[f274,f191,f107,f169])).

fof(f191,plain,
    ( spl3_19
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f274,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_19 ),
    inference(resolution,[],[f192,f65])).

fof(f192,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f191])).

fof(f272,plain,
    ( ~ spl3_19
    | ~ spl3_20
    | ~ spl3_21
    | spl3_32
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f268,f173,f270,f197,f194,f191])).

fof(f268,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_18 ),
    inference(superposition,[],[f68,f174])).

fof(f255,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_31
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f237,f216,f253,f111,f115])).

fof(f115,plain,
    ( spl3_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f111,plain,
    ( spl3_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f237,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_24 ),
    inference(superposition,[],[f61,f217])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f249,plain,
    ( spl3_30
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f234,f216,f154,f247])).

fof(f154,plain,
    ( spl3_16
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f234,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(superposition,[],[f155,f217])).

fof(f155,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f245,plain,
    ( spl3_29
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f233,f216,f149,f243])).

fof(f233,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(superposition,[],[f150,f217])).

fof(f230,plain,
    ( spl3_24
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f228,f212,f134,f216])).

fof(f212,plain,
    ( spl3_23
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f228,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(superposition,[],[f135,f213])).

fof(f213,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f214,plain,
    ( spl3_23
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f210,f149,f212])).

fof(f210,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_15 ),
    inference(resolution,[],[f76,f150])).

fof(f184,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f183,f130,f126,f99,f149])).

fof(f99,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f126,plain,
    ( spl3_11
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f130,plain,
    ( spl3_12
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f183,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f182,f131])).

fof(f131,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f182,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f100,f127])).

fof(f127,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f100,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f180,plain,
    ( ~ spl3_5
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl3_5
    | spl3_17 ),
    inference(subsumption_resolution,[],[f100,f177])).

fof(f177,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_17 ),
    inference(resolution,[],[f170,f74])).

fof(f170,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f169])).

fof(f175,plain,
    ( ~ spl3_17
    | ~ spl3_7
    | spl3_18
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f166,f91,f173,f107,f169])).

fof(f166,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f67,f92])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f156,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f152,f130,f126,f103,f154])).

fof(f103,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f152,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f139,f131])).

fof(f139,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(superposition,[],[f104,f127])).

fof(f104,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f146,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f145,f130,f126,f95,f134])).

fof(f95,plain,
    ( spl3_4
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f145,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f137,f131])).

fof(f137,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(superposition,[],[f96,f127])).

fof(f96,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f132,plain,
    ( spl3_12
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f124,f119,f130])).

fof(f119,plain,
    ( spl3_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f124,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f60,f120])).

% (10496)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f120,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f128,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f123,f111,f126])).

fof(f123,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f60,f112])).

fof(f112,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f121,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f49,f119])).

fof(f49,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f117,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f50,f115])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f113,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f51,f111])).

fof(f51,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f109,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f52,f107])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f105,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f53,f103])).

fof(f53,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f54,f99])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f97,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f55,f95])).

fof(f55,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f56,f91])).

fof(f56,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f57,f87,f84])).

fof(f84,plain,
    ( spl3_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f87,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:57:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (10497)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (10497)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (10510)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (10506)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (10505)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (10491)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (10503)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (10501)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (10498)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (10494)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (10499)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (10502)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f583,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f89,f93,f97,f101,f105,f109,f113,f117,f121,f128,f132,f146,f156,f175,f180,f184,f214,f230,f245,f249,f255,f272,f278,f287,f289,f302,f309,f318,f367,f396,f414,f465,f480,f498,f503,f514,f522,f545,f554,f569,f581,f582])).
% 0.22/0.50  fof(f582,plain,(
% 0.22/0.50    k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f581,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  % (10492)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  fof(f569,plain,(
% 0.22/0.50    ~spl3_44 | spl3_67 | ~spl3_13 | ~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_66),
% 0.22/0.50    inference(avatar_split_clause,[],[f565,f552,f299,f216,f149,f134,f567,f360])).
% 0.22/0.50  fof(f360,plain,(
% 0.22/0.50    spl3_44 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.22/0.50  fof(f567,plain,(
% 0.22/0.50    spl3_67 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    spl3_13 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    spl3_24 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.50  fof(f299,plain,(
% 0.22/0.50    spl3_35 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.50  fof(f552,plain,(
% 0.22/0.50    spl3_66 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.22/0.50  fof(f565,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_66)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f564])).
% 0.22/0.50  fof(f564,plain,(
% 0.22/0.50    k2_struct_0(sK1) != k2_struct_0(sK1) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_66)),
% 0.22/0.50    inference(forward_demodulation,[],[f563,f135])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f134])).
% 0.22/0.50  fof(f563,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_66)),
% 0.22/0.50    inference(forward_demodulation,[],[f562,f300])).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f299])).
% 0.22/0.50  fof(f562,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_66)),
% 0.22/0.50    inference(forward_demodulation,[],[f561,f217])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f216])).
% 0.22/0.50  % (10509)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  fof(f561,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_66)),
% 0.22/0.50    inference(forward_demodulation,[],[f560,f300])).
% 0.22/0.50  fof(f560,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_24 | ~spl3_66)),
% 0.22/0.50    inference(forward_demodulation,[],[f557,f217])).
% 0.22/0.50  fof(f557,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_66)),
% 0.22/0.50    inference(resolution,[],[f553,f150])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f149])).
% 0.22/0.50  fof(f553,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_66),
% 0.22/0.50    inference(avatar_component_clause,[],[f552])).
% 0.22/0.50  fof(f554,plain,(
% 0.22/0.50    ~spl3_7 | spl3_66 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f549,f91,f552,f107])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl3_7 <=> v1_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl3_3 <=> v2_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f549,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f81,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    v2_funct_1(sK2) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f91])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.50  fof(f545,plain,(
% 0.22/0.50    spl3_64 | ~spl3_59),
% 0.22/0.50    inference(avatar_split_clause,[],[f544,f519,f541])).
% 0.22/0.50  fof(f541,plain,(
% 0.22/0.50    spl3_64 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.22/0.50  fof(f519,plain,(
% 0.22/0.50    spl3_59 <=> k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.22/0.50  fof(f544,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_59),
% 0.22/0.50    inference(forward_demodulation,[],[f528,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.50  fof(f528,plain,(
% 0.22/0.50    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k6_relat_1(k1_relat_1(sK2))) | ~spl3_59),
% 0.22/0.50    inference(superposition,[],[f58,f520])).
% 0.22/0.50  fof(f520,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(sK2)) | ~spl3_59),
% 0.22/0.50    inference(avatar_component_clause,[],[f519])).
% 0.22/0.50  fof(f522,plain,(
% 0.22/0.50    ~spl3_17 | ~spl3_7 | ~spl3_3 | spl3_59 | ~spl3_58),
% 0.22/0.50    inference(avatar_split_clause,[],[f517,f512,f519,f91,f107,f169])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    spl3_17 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.50  fof(f512,plain,(
% 0.22/0.50    spl3_58 <=> k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.22/0.50  fof(f517,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_58),
% 0.22/0.50    inference(superposition,[],[f68,f513])).
% 0.22/0.50  fof(f513,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl3_58),
% 0.22/0.50    inference(avatar_component_clause,[],[f512])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.50  fof(f514,plain,(
% 0.22/0.50    ~spl3_17 | ~spl3_7 | spl3_58 | ~spl3_3 | ~spl3_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f510,f173,f91,f512,f107,f169])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    spl3_18 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f510,plain,(
% 0.22/0.50    k6_relat_1(k2_relat_1(k2_funct_1(sK2))) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_3 | ~spl3_18)),
% 0.22/0.50    inference(forward_demodulation,[],[f508,f174])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f173])).
% 0.22/0.50  fof(f508,plain,(
% 0.22/0.50    k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f310,f92])).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0)) = k6_relat_1(k2_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(global_subsumption,[],[f66,f65,f304])).
% 0.22/0.50  fof(f304,plain,(
% 0.22/0.50    ( ! [X0] : (k5_relat_1(k2_funct_1(k2_funct_1(X0)),k2_funct_1(X0)) = k6_relat_1(k2_relat_1(k2_funct_1(X0))) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f69,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f503,plain,(
% 0.22/0.50    spl3_57 | ~spl3_50 | ~spl3_55),
% 0.22/0.50    inference(avatar_split_clause,[],[f499,f478,f392,f501])).
% 0.22/0.50  fof(f501,plain,(
% 0.22/0.50    spl3_57 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.22/0.50  fof(f392,plain,(
% 0.22/0.50    spl3_50 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.22/0.50  fof(f478,plain,(
% 0.22/0.50    spl3_55 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.22/0.50  fof(f499,plain,(
% 0.22/0.50    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_50 | ~spl3_55)),
% 0.22/0.50    inference(forward_demodulation,[],[f493,f393])).
% 0.22/0.50  fof(f393,plain,(
% 0.22/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_50),
% 0.22/0.50    inference(avatar_component_clause,[],[f392])).
% 0.22/0.50  fof(f493,plain,(
% 0.22/0.50    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_55),
% 0.22/0.50    inference(resolution,[],[f479,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f479,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_55),
% 0.22/0.50    inference(avatar_component_clause,[],[f478])).
% 0.22/0.50  fof(f498,plain,(
% 0.22/0.50    spl3_56 | ~spl3_55),
% 0.22/0.50    inference(avatar_split_clause,[],[f492,f478,f496])).
% 0.22/0.50  fof(f496,plain,(
% 0.22/0.50    spl3_56 <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.22/0.50  fof(f492,plain,(
% 0.22/0.50    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_55),
% 0.22/0.50    inference(resolution,[],[f479,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.50  fof(f480,plain,(
% 0.22/0.50    ~spl3_44 | spl3_55 | ~spl3_13 | ~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_54),
% 0.22/0.50    inference(avatar_split_clause,[],[f475,f463,f299,f216,f149,f134,f478,f360])).
% 0.22/0.50  fof(f463,plain,(
% 0.22/0.50    spl3_54 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.22/0.50  fof(f475,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f474,f217])).
% 0.22/0.50  fof(f474,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f473,f300])).
% 0.22/0.50  fof(f473,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_13 | ~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_54)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f472])).
% 0.22/0.50  fof(f472,plain,(
% 0.22/0.50    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_13 | ~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f471,f135])).
% 0.22/0.50  fof(f471,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_15 | ~spl3_24 | ~spl3_35 | ~spl3_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f470,f300])).
% 0.22/0.50  fof(f470,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_15 | ~spl3_24 | ~spl3_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f467,f217])).
% 0.22/0.50  fof(f467,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_15 | ~spl3_54)),
% 0.22/0.50    inference(resolution,[],[f464,f150])).
% 0.22/0.50  fof(f464,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_54),
% 0.22/0.50    inference(avatar_component_clause,[],[f463])).
% 0.22/0.50  fof(f465,plain,(
% 0.22/0.50    ~spl3_7 | spl3_54 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f460,f91,f463,f107])).
% 0.22/0.50  fof(f460,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f80,f92])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.50  fof(f414,plain,(
% 0.22/0.50    ~spl3_30 | spl3_31 | ~spl3_29 | ~spl3_38),
% 0.22/0.50    inference(avatar_split_clause,[],[f408,f316,f243,f253,f247])).
% 0.22/0.50  fof(f247,plain,(
% 0.22/0.50    spl3_30 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    spl3_31 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    spl3_29 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.50  fof(f316,plain,(
% 0.22/0.50    spl3_38 <=> ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),X0) | v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.50  fof(f408,plain,(
% 0.22/0.50    v1_xboole_0(k2_relat_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_29 | ~spl3_38)),
% 0.22/0.50    inference(resolution,[],[f317,f244])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f243])).
% 0.22/0.50  fof(f317,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) | v1_xboole_0(X0) | ~v1_funct_2(sK2,k2_struct_0(sK0),X0)) ) | ~spl3_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f316])).
% 0.22/0.50  fof(f396,plain,(
% 0.22/0.50    spl3_50 | ~spl3_36),
% 0.22/0.50    inference(avatar_split_clause,[],[f395,f307,f392])).
% 0.22/0.50  fof(f307,plain,(
% 0.22/0.50    spl3_36 <=> k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.50  fof(f395,plain,(
% 0.22/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_36),
% 0.22/0.50    inference(forward_demodulation,[],[f379,f58])).
% 0.22/0.50  fof(f379,plain,(
% 0.22/0.50    k1_relat_1(k2_funct_1(sK2)) = k1_relat_1(k6_relat_1(k2_relat_1(sK2))) | ~spl3_36),
% 0.22/0.50    inference(superposition,[],[f58,f308])).
% 0.22/0.50  fof(f308,plain,(
% 0.22/0.50    k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2)) | ~spl3_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f307])).
% 0.22/0.50  fof(f367,plain,(
% 0.22/0.50    spl3_44 | ~spl3_30 | ~spl3_35),
% 0.22/0.50    inference(avatar_split_clause,[],[f345,f299,f247,f360])).
% 0.22/0.50  % (10508)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  fof(f345,plain,(
% 0.22/0.50    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_30 | ~spl3_35)),
% 0.22/0.50    inference(superposition,[],[f248,f300])).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f247])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    ~spl3_7 | spl3_38 | spl3_34),
% 0.22/0.50    inference(avatar_split_clause,[],[f314,f296,f316,f107])).
% 0.22/0.50  fof(f296,plain,(
% 0.22/0.50    spl3_34 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.50  fof(f314,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),X0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) | v1_xboole_0(X0)) ) | spl3_34),
% 0.22/0.50    inference(resolution,[],[f71,f297])).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    ~v1_partfun1(sK2,k2_struct_0(sK0)) | spl3_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f296])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.50    inference(flattening,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.50  fof(f309,plain,(
% 0.22/0.50    ~spl3_17 | ~spl3_7 | spl3_36 | ~spl3_3 | ~spl3_32),
% 0.22/0.50    inference(avatar_split_clause,[],[f305,f270,f91,f307,f107,f169])).
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    spl3_32 <=> k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_3 | ~spl3_32)),
% 0.22/0.50    inference(forward_demodulation,[],[f303,f271])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k5_relat_1(k2_funct_1(sK2),sK2) | ~spl3_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f270])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f69,f92])).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    ~spl3_34 | spl3_35 | ~spl3_29),
% 0.22/0.50    inference(avatar_split_clause,[],[f294,f243,f299,f296])).
% 0.22/0.50  fof(f294,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_29),
% 0.22/0.50    inference(resolution,[],[f204,f244])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1)) )),
% 0.22/0.50    inference(global_subsumption,[],[f74,f203])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.50    inference(resolution,[],[f72,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    ~spl3_17 | ~spl3_7 | ~spl3_3 | spl3_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f288,f197,f91,f107,f169])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    spl3_21 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_21),
% 0.22/0.50    inference(resolution,[],[f198,f64])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ~v2_funct_1(k2_funct_1(sK2)) | spl3_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f197])).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    ~spl3_17 | ~spl3_7 | spl3_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f281,f194,f107,f169])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    spl3_20 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_20),
% 0.22/0.50    inference(resolution,[],[f195,f66])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    ~v1_funct_1(k2_funct_1(sK2)) | spl3_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f194])).
% 0.22/0.50  fof(f278,plain,(
% 0.22/0.50    ~spl3_17 | ~spl3_7 | spl3_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f274,f191,f107,f169])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    spl3_19 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_19),
% 0.22/0.50    inference(resolution,[],[f192,f65])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    ~v1_relat_1(k2_funct_1(sK2)) | spl3_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f191])).
% 0.22/0.50  fof(f272,plain,(
% 0.22/0.50    ~spl3_19 | ~spl3_20 | ~spl3_21 | spl3_32 | ~spl3_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f268,f173,f270,f197,f194,f191])).
% 0.22/0.50  fof(f268,plain,(
% 0.22/0.50    k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_18),
% 0.22/0.50    inference(superposition,[],[f68,f174])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    spl3_9 | ~spl3_8 | ~spl3_31 | ~spl3_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f237,f216,f253,f111,f115])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    spl3_9 <=> v2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl3_8 <=> l1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_24),
% 0.22/0.50    inference(superposition,[],[f61,f217])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    spl3_30 | ~spl3_16 | ~spl3_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f234,f216,f154,f247])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    spl3_16 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_16 | ~spl3_24)),
% 0.22/0.50    inference(superposition,[],[f155,f217])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f154])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    spl3_29 | ~spl3_15 | ~spl3_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f233,f216,f149,f243])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_15 | ~spl3_24)),
% 0.22/0.50    inference(superposition,[],[f150,f217])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    spl3_24 | ~spl3_13 | ~spl3_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f228,f212,f134,f216])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    spl3_23 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_13 | ~spl3_23)),
% 0.22/0.50    inference(superposition,[],[f135,f213])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f212])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    spl3_23 | ~spl3_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f210,f149,f212])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_15),
% 0.22/0.50    inference(resolution,[],[f76,f150])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    spl3_15 | ~spl3_5 | ~spl3_11 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f183,f130,f126,f99,f149])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    spl3_11 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    spl3_12 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_11 | ~spl3_12)),
% 0.22/0.50    inference(forward_demodulation,[],[f182,f131])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f130])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_11)),
% 0.22/0.50    inference(forward_demodulation,[],[f100,f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f126])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ~spl3_5 | spl3_17),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f178])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    $false | (~spl3_5 | spl3_17)),
% 0.22/0.50    inference(subsumption_resolution,[],[f100,f177])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_17),
% 0.22/0.50    inference(resolution,[],[f170,f74])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | spl3_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f169])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    ~spl3_17 | ~spl3_7 | spl3_18 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f166,f91,f173,f107,f169])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f67,f92])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl3_16 | ~spl3_6 | ~spl3_11 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f152,f130,f126,f103,f154])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_11 | ~spl3_12)),
% 0.22/0.50    inference(forward_demodulation,[],[f139,f131])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_11)),
% 0.22/0.50    inference(superposition,[],[f104,f127])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f103])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    spl3_13 | ~spl3_4 | ~spl3_11 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f145,f130,f126,f95,f134])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl3_4 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_11 | ~spl3_12)),
% 0.22/0.50    inference(forward_demodulation,[],[f137,f131])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_11)),
% 0.22/0.50    inference(superposition,[],[f96,f127])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    spl3_12 | ~spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f124,f119,f130])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl3_10 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.22/0.50    inference(resolution,[],[f60,f120])).
% 0.22/0.50  % (10496)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f119])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    spl3_11 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f123,f111,f126])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_8),
% 0.22/0.50    inference(resolution,[],[f60,f112])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    l1_struct_0(sK1) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f111])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f49,f119])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f46,f45,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f16])).
% 0.22/0.50  fof(f16,conjecture,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ~spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f115])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ~v2_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f51,f111])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    l1_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f107])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f53,f103])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f54,f99])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f55,f95])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f56,f91])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    v2_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ~spl3_1 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f87,f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl3_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl3_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (10497)------------------------------
% 0.22/0.51  % (10497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10497)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (10497)Memory used [KB]: 11129
% 0.22/0.51  % (10497)Time elapsed: 0.074 s
% 0.22/0.51  % (10497)------------------------------
% 0.22/0.51  % (10497)------------------------------
% 0.22/0.51  % (10511)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (10490)Success in time 0.148 s
%------------------------------------------------------------------------------
