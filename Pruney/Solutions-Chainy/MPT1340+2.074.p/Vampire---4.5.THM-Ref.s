%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  253 ( 506 expanded)
%              Number of leaves         :   54 ( 212 expanded)
%              Depth                    :   13
%              Number of atoms          : 1000 (1790 expanded)
%              Number of equality atoms :  130 ( 255 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f597,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f105,f110,f115,f120,f125,f145,f152,f186,f191,f206,f210,f221,f241,f269,f270,f288,f299,f336,f349,f354,f431,f438,f464,f469,f488,f494,f499,f515,f573,f594,f596])).

fof(f596,plain,
    ( sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f594,plain,
    ( ~ spl3_1
    | ~ spl3_35
    | ~ spl3_37
    | ~ spl3_46
    | ~ spl3_48 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_35
    | ~ spl3_37
    | ~ spl3_46
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f592,f437])).

fof(f437,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl3_46
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f592,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_35
    | ~ spl3_37
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f591,f75])).

fof(f75,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f591,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_35
    | ~ spl3_37
    | ~ spl3_48 ),
    inference(resolution,[],[f379,f463])).

% (18294)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f463,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f461])).

fof(f461,plain,
    ( spl3_48
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f379,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) )
    | ~ spl3_35
    | ~ spl3_37 ),
    inference(superposition,[],[f344,f353])).

fof(f353,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl3_37
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl3_35
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f573,plain,
    ( spl3_59
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_37
    | ~ spl3_45
    | ~ spl3_52
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f543,f501,f481,f420,f351,f296,f285,f199,f570])).

fof(f570,plain,
    ( spl3_59
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f199,plain,
    ( spl3_19
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f285,plain,
    ( spl3_30
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f296,plain,
    ( spl3_31
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f420,plain,
    ( spl3_45
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f481,plain,
    ( spl3_52
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f501,plain,
    ( spl3_54
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f543,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_37
    | ~ spl3_45
    | ~ spl3_52
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f542,f503])).

fof(f503,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f501])).

fof(f542,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_37
    | ~ spl3_45
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f541,f353])).

fof(f541,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_37
    | ~ spl3_45
    | ~ spl3_52 ),
    inference(forward_demodulation,[],[f540,f353])).

fof(f540,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_45
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f539,f482])).

fof(f482,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f481])).

fof(f539,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f315,f421])).

fof(f421,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f420])).

fof(f315,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_19
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f314,f201])).

fof(f201,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f199])).

fof(f314,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f306,f287])).

fof(f287,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f285])).

fof(f306,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_31 ),
    inference(resolution,[],[f298,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f298,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f296])).

fof(f515,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f499,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f498])).

fof(f498,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | spl3_52 ),
    inference(subsumption_resolution,[],[f497,f204])).

fof(f204,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl3_20
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f497,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_52 ),
    inference(subsumption_resolution,[],[f496,f80])).

fof(f80,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f496,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_52 ),
    inference(subsumption_resolution,[],[f495,f75])).

fof(f495,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_52 ),
    inference(resolution,[],[f483,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f483,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f481])).

fof(f494,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | spl3_51 ),
    inference(avatar_contradiction_clause,[],[f493])).

fof(f493,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | spl3_51 ),
    inference(subsumption_resolution,[],[f492,f204])).

fof(f492,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_51 ),
    inference(subsumption_resolution,[],[f491,f80])).

fof(f491,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_51 ),
    inference(subsumption_resolution,[],[f489,f75])).

fof(f489,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_51 ),
    inference(resolution,[],[f479,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f479,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_51 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl3_51
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f488,plain,
    ( ~ spl3_51
    | ~ spl3_52
    | spl3_53
    | ~ spl3_19
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f470,f420,f199,f485,f481,f477])).

fof(f485,plain,
    ( spl3_53
  <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f470,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_19
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f212,f421])).

fof(f212,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_19 ),
    inference(superposition,[],[f57,f201])).

fof(f57,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f469,plain,
    ( spl3_49
    | ~ spl3_31
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f459,f351,f296,f466])).

fof(f466,plain,
    ( spl3_49
  <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f459,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_31
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f301,f353])).

fof(f301,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_31 ),
    inference(resolution,[],[f298,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f464,plain,
    ( spl3_48
    | ~ spl3_28
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f374,f351,f266,f461])).

fof(f266,plain,
    ( spl3_28
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f374,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_28
    | ~ spl3_37 ),
    inference(superposition,[],[f267,f353])).

fof(f267,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f266])).

fof(f438,plain,
    ( spl3_46
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f408,f351,f231,f149,f435])).

fof(f149,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f231,plain,
    ( spl3_24
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f408,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f252,f353])).

fof(f252,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_24 ),
    inference(superposition,[],[f151,f233])).

fof(f233,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f431,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | spl3_45 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | spl3_45 ),
    inference(subsumption_resolution,[],[f429,f204])).

fof(f429,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_45 ),
    inference(subsumption_resolution,[],[f428,f80])).

fof(f428,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_45 ),
    inference(subsumption_resolution,[],[f425,f75])).

fof(f425,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_45 ),
    inference(resolution,[],[f422,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f422,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_45 ),
    inference(avatar_component_clause,[],[f420])).

fof(f354,plain,
    ( spl3_37
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f273,f262,f203,f188,f351])).

fof(f188,plain,
    ( spl3_17
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f262,plain,
    ( spl3_27
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f273,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f272,f204])).

fof(f272,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_17
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f271,f190])).

fof(f190,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f188])).

fof(f271,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_27 ),
    inference(resolution,[],[f264,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f264,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f262])).

fof(f349,plain,
    ( spl3_35
    | spl3_36
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f341,f266,f231,f149,f73,f346,f343])).

fof(f346,plain,
    ( spl3_36
  <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f341,plain,
    ( ! [X0] :
        ( r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f340,f233])).

fof(f340,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f339,f233])).

fof(f339,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f338,f233])).

fof(f338,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f337,f267])).

fof(f337,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f178,f233])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f169,f75])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f336,plain,
    ( spl3_34
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f326,f266,f231,f218,f149,f78,f73,f333])).

fof(f333,plain,
    ( spl3_34
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f218,plain,
    ( spl3_21
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f326,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f325,f233])).

fof(f325,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f324,f233])).

fof(f324,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f323,f220])).

fof(f220,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f218])).

fof(f323,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f322,f267])).

fof(f322,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f177,f233])).

fof(f177,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f176,f80])).

fof(f176,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f168,f75])).

fof(f168,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f69])).

fof(f299,plain,
    ( spl3_31
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f293,f266,f231,f218,f149,f78,f73,f296])).

fof(f293,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f292,f233])).

% (18275)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f292,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f291,f233])).

fof(f291,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f290,f220])).

fof(f290,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f289,f267])).

fof(f289,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f175,f233])).

fof(f175,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f174,f80])).

fof(f174,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f167,f75])).

fof(f167,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f288,plain,
    ( spl3_30
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f278,f266,f231,f218,f149,f78,f73,f285])).

fof(f278,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f277,f233])).

fof(f277,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f276,f233])).

fof(f276,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f275,f220])).

fof(f275,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f274,f267])).

fof(f274,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f173,f233])).

fof(f173,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f172,f80])).

fof(f172,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f166,f75])).

fof(f166,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f270,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f269,plain,
    ( spl3_27
    | ~ spl3_28
    | ~ spl3_1
    | spl3_12
    | ~ spl3_13
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f260,f231,f149,f142,f73,f266,f262])).

fof(f142,plain,
    ( spl3_12
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f260,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | spl3_12
    | ~ spl3_13
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f171,f233])).

fof(f171,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f170,f75])).

fof(f170,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f162,f144])).

fof(f144,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f162,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f241,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f221,plain,
    ( spl3_21
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f163,f149,f218])).

fof(f163,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f63])).

fof(f210,plain,
    ( ~ spl3_13
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl3_13
    | spl3_20 ),
    inference(subsumption_resolution,[],[f208,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f208,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_13
    | spl3_20 ),
    inference(resolution,[],[f207,f151])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_20 ),
    inference(resolution,[],[f205,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
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

fof(f205,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f203])).

fof(f206,plain,
    ( spl3_19
    | ~ spl3_20
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f98,f78,f73,f203,f199])).

fof(f98,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f97,f75])).

fof(f97,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f80,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f191,plain,
    ( spl3_17
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f164,f149,f188])).

fof(f164,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f186,plain,
    ( ~ spl3_16
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f181,f117,f107,f183])).

fof(f183,plain,
    ( spl3_16
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f107,plain,
    ( spl3_7
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f117,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f181,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f180,f119])).

fof(f119,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f180,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f46,f109])).

fof(f109,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f46,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f152,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f140,f117,f112,f107,f149])).

fof(f112,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f134,f119])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f114,f109])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f145,plain,
    ( ~ spl3_12
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f133,f107,f88,f83,f142])).

fof(f83,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f88,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f133,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f132,f85])).

fof(f85,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f132,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f131,f90])).

fof(f90,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f131,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f52,f109])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f125,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f44,f122])).

fof(f122,plain,
    ( spl3_10
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f44,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f120,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f100,f93,f117])).

fof(f93,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f100,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f95,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f95,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f115,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f43,f112])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f99,f88,f107])).

fof(f99,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f90,f50])).

fof(f105,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f42,f102])).

fof(f102,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f42,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f49,f93])).

fof(f49,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f48,f88])).

fof(f48,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f47,f83])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f45,f78])).

% (18276)Refutation not found, incomplete strategy% (18276)------------------------------
% (18276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18276)Termination reason: Refutation not found, incomplete strategy

% (18276)Memory used [KB]: 10746
% (18276)Time elapsed: 0.048 s
% (18276)------------------------------
% (18276)------------------------------
fof(f45,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f41,f73])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:50:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (18278)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (18284)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (18293)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (18276)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (18288)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (18289)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (18277)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (18286)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (18285)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (18288)Refutation not found, incomplete strategy% (18288)------------------------------
% 0.20/0.48  % (18288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18288)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (18288)Memory used [KB]: 1663
% 0.20/0.48  % (18288)Time elapsed: 0.067 s
% 0.20/0.48  % (18288)------------------------------
% 0.20/0.48  % (18288)------------------------------
% 0.20/0.48  % (18282)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (18280)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (18291)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (18278)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f597,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f105,f110,f115,f120,f125,f145,f152,f186,f191,f206,f210,f221,f241,f269,f270,f288,f299,f336,f349,f354,f431,f438,f464,f469,f488,f494,f499,f515,f573,f594,f596])).
% 0.20/0.48  fof(f596,plain,(
% 0.20/0.48    sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f594,plain,(
% 0.20/0.48    ~spl3_1 | ~spl3_35 | ~spl3_37 | ~spl3_46 | ~spl3_48),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f593])).
% 0.20/0.48  fof(f593,plain,(
% 0.20/0.48    $false | (~spl3_1 | ~spl3_35 | ~spl3_37 | ~spl3_46 | ~spl3_48)),
% 0.20/0.48    inference(subsumption_resolution,[],[f592,f437])).
% 0.20/0.48  fof(f437,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_46),
% 0.20/0.48    inference(avatar_component_clause,[],[f435])).
% 0.20/0.48  fof(f435,plain,(
% 0.20/0.48    spl3_46 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.20/0.48  fof(f592,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_35 | ~spl3_37 | ~spl3_48)),
% 0.20/0.48    inference(subsumption_resolution,[],[f591,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    v1_funct_1(sK2) | ~spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    spl3_1 <=> v1_funct_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f591,plain,(
% 0.20/0.48    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_35 | ~spl3_37 | ~spl3_48)),
% 0.20/0.48    inference(resolution,[],[f379,f463])).
% 0.20/0.49  % (18294)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  fof(f463,plain,(
% 0.20/0.49    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_48),
% 0.20/0.49    inference(avatar_component_clause,[],[f461])).
% 0.20/0.49  fof(f461,plain,(
% 0.20/0.49    spl3_48 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.49  fof(f379,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))) ) | (~spl3_35 | ~spl3_37)),
% 0.20/0.49    inference(superposition,[],[f344,f353])).
% 0.20/0.49  fof(f353,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_37),
% 0.20/0.49    inference(avatar_component_clause,[],[f351])).
% 0.20/0.49  fof(f351,plain,(
% 0.20/0.49    spl3_37 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.49  fof(f344,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))) ) | ~spl3_35),
% 0.20/0.49    inference(avatar_component_clause,[],[f343])).
% 0.20/0.49  fof(f343,plain,(
% 0.20/0.49    spl3_35 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.49  fof(f573,plain,(
% 0.20/0.49    spl3_59 | ~spl3_19 | ~spl3_30 | ~spl3_31 | ~spl3_37 | ~spl3_45 | ~spl3_52 | ~spl3_54),
% 0.20/0.49    inference(avatar_split_clause,[],[f543,f501,f481,f420,f351,f296,f285,f199,f570])).
% 0.20/0.49  fof(f570,plain,(
% 0.20/0.49    spl3_59 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl3_19 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.49  fof(f285,plain,(
% 0.20/0.49    spl3_30 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.49  fof(f296,plain,(
% 0.20/0.49    spl3_31 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.49  fof(f420,plain,(
% 0.20/0.49    spl3_45 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.49  fof(f481,plain,(
% 0.20/0.49    spl3_52 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.20/0.49  fof(f501,plain,(
% 0.20/0.49    spl3_54 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.20/0.49  fof(f543,plain,(
% 0.20/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_19 | ~spl3_30 | ~spl3_31 | ~spl3_37 | ~spl3_45 | ~spl3_52 | ~spl3_54)),
% 0.20/0.49    inference(subsumption_resolution,[],[f542,f503])).
% 0.20/0.49  fof(f503,plain,(
% 0.20/0.49    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_54),
% 0.20/0.49    inference(avatar_component_clause,[],[f501])).
% 0.20/0.49  fof(f542,plain,(
% 0.20/0.49    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_19 | ~spl3_30 | ~spl3_31 | ~spl3_37 | ~spl3_45 | ~spl3_52)),
% 0.20/0.49    inference(forward_demodulation,[],[f541,f353])).
% 0.20/0.49  fof(f541,plain,(
% 0.20/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_19 | ~spl3_30 | ~spl3_31 | ~spl3_37 | ~spl3_45 | ~spl3_52)),
% 0.20/0.49    inference(forward_demodulation,[],[f540,f353])).
% 0.20/0.49  fof(f540,plain,(
% 0.20/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_19 | ~spl3_30 | ~spl3_31 | ~spl3_45 | ~spl3_52)),
% 0.20/0.49    inference(subsumption_resolution,[],[f539,f482])).
% 0.20/0.49  fof(f482,plain,(
% 0.20/0.49    v2_funct_1(k2_funct_1(sK2)) | ~spl3_52),
% 0.20/0.49    inference(avatar_component_clause,[],[f481])).
% 0.20/0.49  fof(f539,plain,(
% 0.20/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_19 | ~spl3_30 | ~spl3_31 | ~spl3_45)),
% 0.20/0.49    inference(subsumption_resolution,[],[f315,f421])).
% 0.20/0.49  fof(f421,plain,(
% 0.20/0.49    v1_funct_1(k2_funct_1(sK2)) | ~spl3_45),
% 0.20/0.49    inference(avatar_component_clause,[],[f420])).
% 0.20/0.49  fof(f315,plain,(
% 0.20/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_19 | ~spl3_30 | ~spl3_31)),
% 0.20/0.49    inference(forward_demodulation,[],[f314,f201])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_19),
% 0.20/0.49    inference(avatar_component_clause,[],[f199])).
% 0.20/0.49  fof(f314,plain,(
% 0.20/0.49    ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_30 | ~spl3_31)),
% 0.20/0.49    inference(subsumption_resolution,[],[f306,f287])).
% 0.20/0.49  fof(f287,plain,(
% 0.20/0.49    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_30),
% 0.20/0.49    inference(avatar_component_clause,[],[f285])).
% 0.20/0.49  fof(f306,plain,(
% 0.20/0.49    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_31),
% 0.20/0.49    inference(resolution,[],[f298,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.49  fof(f298,plain,(
% 0.20/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_31),
% 0.20/0.49    inference(avatar_component_clause,[],[f296])).
% 0.20/0.49  fof(f515,plain,(
% 0.20/0.49    k2_relat_1(k2_funct_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f499,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2 | ~spl3_20 | spl3_52),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f498])).
% 0.20/0.49  fof(f498,plain,(
% 0.20/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_20 | spl3_52)),
% 0.20/0.49    inference(subsumption_resolution,[],[f497,f204])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl3_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f203])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    spl3_20 <=> v1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.49  fof(f497,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | spl3_52)),
% 0.20/0.49    inference(subsumption_resolution,[],[f496,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    v2_funct_1(sK2) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    spl3_2 <=> v2_funct_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f496,plain,(
% 0.20/0.49    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_52)),
% 0.20/0.49    inference(subsumption_resolution,[],[f495,f75])).
% 0.20/0.49  fof(f495,plain,(
% 0.20/0.49    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_52),
% 0.20/0.49    inference(resolution,[],[f483,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.20/0.49  fof(f483,plain,(
% 0.20/0.49    ~v2_funct_1(k2_funct_1(sK2)) | spl3_52),
% 0.20/0.49    inference(avatar_component_clause,[],[f481])).
% 0.20/0.49  fof(f494,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2 | ~spl3_20 | spl3_51),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f493])).
% 0.20/0.49  fof(f493,plain,(
% 0.20/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_20 | spl3_51)),
% 0.20/0.49    inference(subsumption_resolution,[],[f492,f204])).
% 0.20/0.49  fof(f492,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | spl3_51)),
% 0.20/0.49    inference(subsumption_resolution,[],[f491,f80])).
% 0.20/0.49  fof(f491,plain,(
% 0.20/0.49    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_51)),
% 0.20/0.49    inference(subsumption_resolution,[],[f489,f75])).
% 0.20/0.49  fof(f489,plain,(
% 0.20/0.49    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_51),
% 0.20/0.49    inference(resolution,[],[f479,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f479,plain,(
% 0.20/0.49    ~v1_relat_1(k2_funct_1(sK2)) | spl3_51),
% 0.20/0.49    inference(avatar_component_clause,[],[f477])).
% 0.20/0.49  fof(f477,plain,(
% 0.20/0.49    spl3_51 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.20/0.49  fof(f488,plain,(
% 0.20/0.49    ~spl3_51 | ~spl3_52 | spl3_53 | ~spl3_19 | ~spl3_45),
% 0.20/0.49    inference(avatar_split_clause,[],[f470,f420,f199,f485,f481,f477])).
% 0.20/0.49  fof(f485,plain,(
% 0.20/0.49    spl3_53 <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.20/0.49  fof(f470,plain,(
% 0.20/0.49    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_19 | ~spl3_45)),
% 0.20/0.49    inference(subsumption_resolution,[],[f212,f421])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_19),
% 0.20/0.49    inference(superposition,[],[f57,f201])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.49  fof(f469,plain,(
% 0.20/0.49    spl3_49 | ~spl3_31 | ~spl3_37),
% 0.20/0.49    inference(avatar_split_clause,[],[f459,f351,f296,f466])).
% 0.20/0.49  fof(f466,plain,(
% 0.20/0.49    spl3_49 <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.20/0.49  fof(f459,plain,(
% 0.20/0.49    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_31 | ~spl3_37)),
% 0.20/0.49    inference(forward_demodulation,[],[f301,f353])).
% 0.20/0.49  fof(f301,plain,(
% 0.20/0.49    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_31),
% 0.20/0.49    inference(resolution,[],[f298,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.49  fof(f464,plain,(
% 0.20/0.49    spl3_48 | ~spl3_28 | ~spl3_37),
% 0.20/0.49    inference(avatar_split_clause,[],[f374,f351,f266,f461])).
% 0.20/0.49  fof(f266,plain,(
% 0.20/0.49    spl3_28 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.49  fof(f374,plain,(
% 0.20/0.49    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_28 | ~spl3_37)),
% 0.20/0.49    inference(superposition,[],[f267,f353])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_28),
% 0.20/0.49    inference(avatar_component_clause,[],[f266])).
% 0.20/0.49  fof(f438,plain,(
% 0.20/0.49    spl3_46 | ~spl3_13 | ~spl3_24 | ~spl3_37),
% 0.20/0.49    inference(avatar_split_clause,[],[f408,f351,f231,f149,f435])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f231,plain,(
% 0.20/0.49    spl3_24 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.49  fof(f408,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_24 | ~spl3_37)),
% 0.20/0.49    inference(forward_demodulation,[],[f252,f353])).
% 0.20/0.49  fof(f252,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_24)),
% 0.20/0.49    inference(superposition,[],[f151,f233])).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f231])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f149])).
% 0.20/0.49  fof(f431,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2 | ~spl3_20 | spl3_45),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f430])).
% 0.20/0.49  fof(f430,plain,(
% 0.20/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_20 | spl3_45)),
% 0.20/0.49    inference(subsumption_resolution,[],[f429,f204])).
% 0.20/0.49  fof(f429,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | spl3_45)),
% 0.20/0.49    inference(subsumption_resolution,[],[f428,f80])).
% 0.20/0.49  fof(f428,plain,(
% 0.20/0.49    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_45)),
% 0.20/0.49    inference(subsumption_resolution,[],[f425,f75])).
% 0.20/0.49  fof(f425,plain,(
% 0.20/0.49    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_45),
% 0.20/0.49    inference(resolution,[],[f422,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f422,plain,(
% 0.20/0.49    ~v1_funct_1(k2_funct_1(sK2)) | spl3_45),
% 0.20/0.49    inference(avatar_component_clause,[],[f420])).
% 0.20/0.49  fof(f354,plain,(
% 0.20/0.49    spl3_37 | ~spl3_17 | ~spl3_20 | ~spl3_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f273,f262,f203,f188,f351])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    spl3_17 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.49  fof(f262,plain,(
% 0.20/0.49    spl3_27 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_17 | ~spl3_20 | ~spl3_27)),
% 0.20/0.49    inference(subsumption_resolution,[],[f272,f204])).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_17 | ~spl3_27)),
% 0.20/0.49    inference(subsumption_resolution,[],[f271,f190])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f188])).
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_27),
% 0.20/0.49    inference(resolution,[],[f264,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.49  fof(f264,plain,(
% 0.20/0.49    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f262])).
% 0.20/0.49  fof(f349,plain,(
% 0.20/0.49    spl3_35 | spl3_36 | ~spl3_1 | ~spl3_13 | ~spl3_24 | ~spl3_28),
% 0.20/0.49    inference(avatar_split_clause,[],[f341,f266,f231,f149,f73,f346,f343])).
% 0.20/0.49  fof(f346,plain,(
% 0.20/0.49    spl3_36 <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.49  fof(f341,plain,(
% 0.20/0.49    ( ! [X0] : (r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0)) ) | (~spl3_1 | ~spl3_13 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(forward_demodulation,[],[f340,f233])).
% 0.20/0.49  fof(f340,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(forward_demodulation,[],[f339,f233])).
% 0.20/0.49  fof(f339,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(forward_demodulation,[],[f338,f233])).
% 0.20/0.49  fof(f338,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(subsumption_resolution,[],[f337,f267])).
% 0.20/0.49  fof(f337,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_24)),
% 0.20/0.49    inference(forward_demodulation,[],[f178,f233])).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f169,f75])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | ~spl3_13),
% 0.20/0.49    inference(resolution,[],[f151,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.20/0.49  fof(f336,plain,(
% 0.20/0.49    spl3_34 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28),
% 0.20/0.49    inference(avatar_split_clause,[],[f326,f266,f231,f218,f149,f78,f73,f333])).
% 0.20/0.49  fof(f333,plain,(
% 0.20/0.49    spl3_34 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    spl3_21 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f326,plain,(
% 0.20/0.49    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(forward_demodulation,[],[f325,f233])).
% 0.20/0.49  fof(f325,plain,(
% 0.20/0.49    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(subsumption_resolution,[],[f324,f233])).
% 0.20/0.49  fof(f324,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_relat_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(forward_demodulation,[],[f323,f220])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f218])).
% 0.20/0.49  fof(f323,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(subsumption_resolution,[],[f322,f267])).
% 0.20/0.49  fof(f322,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_24)),
% 0.20/0.49    inference(forward_demodulation,[],[f177,f233])).
% 0.20/0.49  fof(f177,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f176,f80])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f168,f75])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.20/0.49    inference(resolution,[],[f151,f69])).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    spl3_31 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28),
% 0.20/0.49    inference(avatar_split_clause,[],[f293,f266,f231,f218,f149,f78,f73,f296])).
% 0.20/0.49  fof(f293,plain,(
% 0.20/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(forward_demodulation,[],[f292,f233])).
% 0.20/0.49  % (18275)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  fof(f292,plain,(
% 0.20/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(subsumption_resolution,[],[f291,f233])).
% 0.20/0.49  fof(f291,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(forward_demodulation,[],[f290,f220])).
% 0.20/0.49  fof(f290,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(subsumption_resolution,[],[f289,f267])).
% 0.20/0.49  fof(f289,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_24)),
% 0.20/0.49    inference(forward_demodulation,[],[f175,f233])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f174,f80])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f167,f75])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl3_13),
% 0.20/0.49    inference(resolution,[],[f151,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    spl3_30 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28),
% 0.20/0.49    inference(avatar_split_clause,[],[f278,f266,f231,f218,f149,f78,f73,f285])).
% 0.20/0.49  fof(f278,plain,(
% 0.20/0.49    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(forward_demodulation,[],[f277,f233])).
% 0.20/0.49  fof(f277,plain,(
% 0.20/0.49    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(subsumption_resolution,[],[f276,f233])).
% 0.20/0.49  fof(f276,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(forward_demodulation,[],[f275,f220])).
% 0.20/0.49  fof(f275,plain,(
% 0.20/0.49    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_24 | ~spl3_28)),
% 0.20/0.49    inference(subsumption_resolution,[],[f274,f267])).
% 0.20/0.49  fof(f274,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_24)),
% 0.20/0.49    inference(forward_demodulation,[],[f173,f233])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f172,f80])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f166,f75])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~spl3_13),
% 0.20/0.49    inference(resolution,[],[f151,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f270,plain,(
% 0.20/0.49    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | u1_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f269,plain,(
% 0.20/0.49    spl3_27 | ~spl3_28 | ~spl3_1 | spl3_12 | ~spl3_13 | ~spl3_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f260,f231,f149,f142,f73,f266,f262])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    spl3_12 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.49  fof(f260,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | spl3_12 | ~spl3_13 | ~spl3_24)),
% 0.20/0.49    inference(forward_demodulation,[],[f171,f233])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | spl3_12 | ~spl3_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f170,f75])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (spl3_12 | ~spl3_13)),
% 0.20/0.49    inference(subsumption_resolution,[],[f162,f144])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f142])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.20/0.49    inference(resolution,[],[f151,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.49    inference(flattening,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f221,plain,(
% 0.20/0.49    spl3_21 | ~spl3_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f163,f149,f218])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_13),
% 0.20/0.49    inference(resolution,[],[f151,f63])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    ~spl3_13 | spl3_20),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f209])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    $false | (~spl3_13 | spl3_20)),
% 0.20/0.49    inference(subsumption_resolution,[],[f208,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_13 | spl3_20)),
% 0.20/0.49    inference(resolution,[],[f207,f151])).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_20),
% 0.20/0.49    inference(resolution,[],[f205,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | spl3_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f203])).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    spl3_19 | ~spl3_20 | ~spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f98,f78,f73,f203,f199])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f97,f75])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.20/0.49    inference(resolution,[],[f80,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    spl3_17 | ~spl3_13),
% 0.20/0.49    inference(avatar_split_clause,[],[f164,f149,f188])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.20/0.49    inference(resolution,[],[f151,f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    ~spl3_16 | ~spl3_7 | ~spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f181,f117,f107,f183])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    spl3_16 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    spl3_7 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_7 | ~spl3_9)),
% 0.20/0.49    inference(forward_demodulation,[],[f180,f119])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f117])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~spl3_7),
% 0.20/0.49    inference(forward_demodulation,[],[f46,f109])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f107])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.49    inference(negated_conjecture,[],[f15])).
% 0.20/0.49  fof(f15,conjecture,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    spl3_13 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f140,f117,f112,f107,f149])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.20/0.49    inference(forward_demodulation,[],[f134,f119])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8)),
% 0.20/0.49    inference(forward_demodulation,[],[f114,f109])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f112])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ~spl3_12 | spl3_3 | ~spl3_4 | ~spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f133,f107,f88,f83,f142])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl3_3 <=> v2_struct_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl3_4 <=> l1_struct_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | (spl3_3 | ~spl3_4 | ~spl3_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f132,f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ~v2_struct_0(sK1) | spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f83])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f131,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    l1_struct_0(sK1) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f88])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_7),
% 0.20/0.49    inference(superposition,[],[f52,f109])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    spl3_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    spl3_10 <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    spl3_9 | ~spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f100,f93,f117])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl3_5 <=> l1_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.20/0.49    inference(resolution,[],[f95,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    l1_struct_0(sK0) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f93])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f112])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    spl3_7 | ~spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f99,f88,f107])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_4),
% 0.20/0.49    inference(resolution,[],[f90,f50])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f42,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f49,f93])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    l1_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f48,f88])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    l1_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f47,f83])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ~v2_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f78])).
% 0.20/0.49  % (18276)Refutation not found, incomplete strategy% (18276)------------------------------
% 0.20/0.49  % (18276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18276)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18276)Memory used [KB]: 10746
% 0.20/0.49  % (18276)Time elapsed: 0.048 s
% 0.20/0.49  % (18276)------------------------------
% 0.20/0.49  % (18276)------------------------------
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    v2_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f73])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (18278)------------------------------
% 0.20/0.49  % (18278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18278)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (18278)Memory used [KB]: 11001
% 0.20/0.49  % (18278)Time elapsed: 0.077 s
% 0.20/0.49  % (18278)------------------------------
% 0.20/0.49  % (18278)------------------------------
% 0.20/0.49  % (18279)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (18274)Success in time 0.139 s
%------------------------------------------------------------------------------
