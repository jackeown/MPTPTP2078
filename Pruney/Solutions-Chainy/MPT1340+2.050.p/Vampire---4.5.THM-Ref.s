%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  288 ( 584 expanded)
%              Number of leaves         :   62 ( 252 expanded)
%              Depth                    :   18
%              Number of atoms          : 1201 (2059 expanded)
%              Number of equality atoms :  161 ( 312 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f648,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f124,f129,f134,f139,f144,f164,f171,f208,f213,f228,f232,f242,f266,f267,f288,f291,f315,f324,f325,f365,f370,f402,f445,f466,f493,f498,f527,f534,f553,f562,f566,f586,f646,f647])).

fof(f647,plain,
    ( k1_relat_1(sK2) != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k4_relat_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f646,plain,
    ( spl3_60
    | ~ spl3_22
    | ~ spl3_29
    | ~ spl3_37
    | ~ spl3_48
    | ~ spl3_53
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f641,f568,f559,f531,f399,f312,f244,f643])).

fof(f643,plain,
    ( spl3_60
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f244,plain,
    ( spl3_22
  <=> sK2 = k2_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f312,plain,
    ( spl3_29
  <=> v1_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f399,plain,
    ( spl3_37
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f531,plain,
    ( spl3_48
  <=> v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f559,plain,
    ( spl3_53
  <=> v2_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f568,plain,
    ( spl3_54
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f641,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_22
    | ~ spl3_29
    | ~ spl3_37
    | ~ spl3_48
    | ~ spl3_53
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f640,f561])).

fof(f561,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f559])).

fof(f640,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ spl3_22
    | ~ spl3_29
    | ~ spl3_37
    | ~ spl3_48
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f639,f570])).

fof(f570,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f568])).

fof(f639,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ spl3_22
    | ~ spl3_29
    | ~ spl3_37
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f427,f533])).

fof(f533,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f531])).

fof(f427,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ spl3_22
    | ~ spl3_29
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f426,f246])).

fof(f246,plain,
    ( sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f244])).

fof(f426,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | k2_funct_1(k4_relat_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_29
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f417,f314])).

fof(f314,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f312])).

fof(f417,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | k2_funct_1(k4_relat_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_37 ),
    inference(resolution,[],[f401,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f401,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f399])).

fof(f586,plain,
    ( k2_relat_1(k4_relat_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f566,plain,
    ( ~ spl3_20
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl3_20
    | spl3_52 ),
    inference(subsumption_resolution,[],[f564,f226])).

fof(f226,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl3_20
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f564,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_52 ),
    inference(trivial_inequality_removal,[],[f563])).

fof(f563,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_52 ),
    inference(superposition,[],[f557,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f557,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f555])).

fof(f555,plain,
    ( spl3_52
  <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f562,plain,
    ( ~ spl3_52
    | spl3_53
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f349,f312,f285,f239,f225,f93,f88,f559,f555])).

fof(f88,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f93,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f239,plain,
    ( spl3_21
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f285,plain,
    ( spl3_27
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f349,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f348,f241])).

fof(f241,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f239])).

fof(f348,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f347,f241])).

fof(f347,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f346,f287])).

fof(f287,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f285])).

fof(f346,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f345,f241])).

fof(f345,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_21
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f344,f314])).

% (6538)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f344,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f343,f241])).

fof(f343,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f342,f226])).

fof(f342,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f341,f95])).

fof(f95,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f341,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f340,f90])).

fof(f90,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f340,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f339,f60])).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f339,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_20 ),
    inference(superposition,[],[f333,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f333,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(k5_relat_1(X0,sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | v2_funct_1(X0) )
    | ~ spl3_1
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f112,f226])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK2))
        | k2_relat_1(X0) != k1_relat_1(sK2)
        | v2_funct_1(X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f90,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f553,plain,
    ( spl3_51
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f411,f399,f550])).

fof(f550,plain,
    ( spl3_51
  <=> k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f411,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_37 ),
    inference(resolution,[],[f401,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f534,plain,
    ( spl3_48
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f393,f367,f362,f531])).

fof(f362,plain,
    ( spl3_33
  <=> v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f367,plain,
    ( spl3_34
  <=> k1_relat_1(sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f393,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(superposition,[],[f364,f369])).

fof(f369,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f367])).

fof(f364,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f362])).

fof(f527,plain,
    ( ~ spl3_1
    | ~ spl3_42
    | ~ spl3_46
    | ~ spl3_47 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_42
    | ~ spl3_46
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f525,f492])).

fof(f492,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f490])).

fof(f490,plain,
    ( spl3_46
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f525,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_42
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f524,f90])).

fof(f524,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_42
    | ~ spl3_47 ),
    inference(resolution,[],[f497,f461])).

fof(f461,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) )
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl3_42
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f497,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f495])).

fof(f495,plain,
    ( spl3_47
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f498,plain,
    ( spl3_47
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f392,f367,f321,f495])).

fof(f321,plain,
    ( spl3_31
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f392,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(superposition,[],[f322,f369])).

fof(f322,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f321])).

fof(f493,plain,
    ( spl3_46
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f487,f367,f277,f168,f490])).

fof(f168,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f277,plain,
    ( spl3_26
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f487,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f302,f369])).

fof(f302,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(superposition,[],[f170,f279])).

fof(f279,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f277])).

fof(f170,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f466,plain,
    ( spl3_42
    | spl3_43
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f458,f367,f321,f277,f168,f88,f463,f460])).

fof(f463,plain,
    ( spl3_43
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f458,plain,
    ( ! [X0] :
        ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f457,f369])).

fof(f457,plain,
    ( ! [X0] :
        ( r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f456,f279])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f455,f369])).

fof(f455,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f454,f279])).

fof(f454,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f453,f369])).

fof(f453,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f452,f279])).

fof(f452,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f451,f322])).

fof(f451,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f200,f279])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f189,f90])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_13 ),
    inference(resolution,[],[f170,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f445,plain,
    ( spl3_40
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f435,f367,f321,f277,f263,f239,f168,f93,f88,f442])).

fof(f442,plain,
    ( spl3_40
  <=> k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f263,plain,
    ( spl3_23
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f435,plain,
    ( k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f434,f241])).

fof(f434,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f433,f369])).

fof(f433,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f432,f279])).

fof(f432,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f431,f279])).

fof(f431,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f430,f265])).

fof(f265,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f263])).

fof(f430,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f429,f322])).

fof(f429,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f199,f279])).

fof(f199,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f198,f95])).

fof(f198,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f188,f90])).

fof(f188,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f170,f84])).

fof(f402,plain,
    ( spl3_37
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f397,f367,f321,f277,f263,f239,f168,f93,f88,f399])).

fof(f397,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f384,f369])).

fof(f384,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f383,f241])).

fof(f383,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f382,f279])).

fof(f382,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f381,f279])).

fof(f381,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f380,f265])).

fof(f380,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f379,f322])).

fof(f379,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f197,f279])).

fof(f197,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f196,f95])).

fof(f196,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f187,f90])).

fof(f187,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_13 ),
    inference(resolution,[],[f170,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f370,plain,
    ( spl3_34
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f332,f317,f225,f210,f367])).

fof(f210,plain,
    ( spl3_17
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f317,plain,
    ( spl3_30
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f332,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ spl3_17
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f331,f226])).

fof(f331,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_17
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f330,f212])).

fof(f212,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f210])).

fof(f330,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_30 ),
    inference(resolution,[],[f319,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f319,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f317])).

fof(f365,plain,
    ( spl3_33
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f360,f321,f277,f263,f239,f168,f93,f88,f362])).

fof(f360,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f359,f241])).

fof(f359,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f358,f279])).

fof(f358,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f357,f279])).

fof(f357,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f356,f265])).

fof(f356,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_26
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f355,f322])).

fof(f355,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f195,f279])).

fof(f195,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f194,f95])).

fof(f194,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f186,f90])).

fof(f186,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f170,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f325,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f324,plain,
    ( spl3_30
    | ~ spl3_31
    | ~ spl3_1
    | spl3_12
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f310,f277,f168,f161,f88,f321,f317])).

fof(f161,plain,
    ( spl3_12
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f310,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | spl3_12
    | ~ spl3_13
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f191,f279])).

fof(f191,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f190,f90])).

fof(f190,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f181,f163])).

fof(f163,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f181,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f170,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f315,plain,
    ( spl3_29
    | ~ spl3_1
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f261,f239,f225,f88,f312])).

fof(f261,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f260,f226])).

fof(f260,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f251,f90])).

fof(f251,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(superposition,[],[f67,f241])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f291,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f288,plain,
    ( spl3_27
    | ~ spl3_1
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f259,f239,f225,f88,f285])).

fof(f259,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f258,f226])).

fof(f258,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f250,f90])).

fof(f250,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(superposition,[],[f66,f241])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f267,plain,
    ( k2_funct_1(sK2) != k4_relat_1(sK2)
    | sK2 != k2_funct_1(k2_funct_1(sK2))
    | sK2 = k2_funct_1(k4_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f266,plain,
    ( spl3_23
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f182,f168,f263])).

fof(f182,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f170,f78])).

fof(f242,plain,
    ( spl3_21
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f237,f225,f93,f88,f239])).

fof(f237,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f117,f226])).

fof(f117,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f115,f90])).

fof(f115,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f95,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f232,plain,
    ( ~ spl3_13
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl3_13
    | spl3_20 ),
    inference(subsumption_resolution,[],[f230,f74])).

fof(f74,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f230,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_13
    | spl3_20 ),
    inference(resolution,[],[f229,f170])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_20 ),
    inference(resolution,[],[f227,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f227,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f225])).

fof(f228,plain,
    ( spl3_19
    | ~ spl3_20
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f116,f93,f88,f225,f221])).

fof(f221,plain,
    ( spl3_19
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f116,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f114,f90])).

fof(f114,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f95,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f213,plain,
    ( spl3_17
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f183,f168,f210])).

fof(f183,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f170,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f208,plain,
    ( ~ spl3_16
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f203,f136,f126,f205])).

fof(f205,plain,
    ( spl3_16
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f126,plain,
    ( spl3_7
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f136,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f203,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f202,f138])).

fof(f138,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f202,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f55,f128])).

fof(f128,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f55,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f171,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f159,f136,f131,f126,f168])).

fof(f131,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f159,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f153,f138])).

fof(f153,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f133,f128])).

fof(f133,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f164,plain,
    ( ~ spl3_12
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f152,f126,f103,f98,f161])).

fof(f98,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f103,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f152,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f151,f100])).

fof(f100,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f151,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f150,f105])).

fof(f105,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f150,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f65,f128])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f144,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f53,f141])).

fof(f141,plain,
    ( spl3_10
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f53,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f139,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f119,f108,f136])).

fof(f108,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f110,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f110,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f134,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f52,f131])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f129,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f118,f103,f126])).

fof(f118,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f105,f61])).

fof(f124,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f51,f121])).

fof(f121,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f111,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f58,f108])).

fof(f58,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f106,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f57,f103])).

fof(f57,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f56,f98])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f54,f93])).

fof(f54,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f50,f88])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (6551)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (6536)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (6536)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (6537)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f648,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f124,f129,f134,f139,f144,f164,f171,f208,f213,f228,f232,f242,f266,f267,f288,f291,f315,f324,f325,f365,f370,f402,f445,f466,f493,f498,f527,f534,f553,f562,f566,f586,f646,f647])).
% 0.21/0.48  fof(f647,plain,(
% 0.21/0.48    k1_relat_1(sK2) != k2_struct_0(sK0) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k4_relat_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f646,plain,(
% 0.21/0.48    spl3_60 | ~spl3_22 | ~spl3_29 | ~spl3_37 | ~spl3_48 | ~spl3_53 | ~spl3_54),
% 0.21/0.48    inference(avatar_split_clause,[],[f641,f568,f559,f531,f399,f312,f244,f643])).
% 0.21/0.48  fof(f643,plain,(
% 0.21/0.48    spl3_60 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    spl3_22 <=> sK2 = k2_funct_1(k4_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.48  fof(f312,plain,(
% 0.21/0.48    spl3_29 <=> v1_funct_1(k4_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.48  fof(f399,plain,(
% 0.21/0.48    spl3_37 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.48  fof(f531,plain,(
% 0.21/0.48    spl3_48 <=> v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.48  fof(f559,plain,(
% 0.21/0.48    spl3_53 <=> v2_funct_1(k4_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.21/0.48  fof(f568,plain,(
% 0.21/0.48    spl3_54 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.48  fof(f641,plain,(
% 0.21/0.48    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | (~spl3_22 | ~spl3_29 | ~spl3_37 | ~spl3_48 | ~spl3_53 | ~spl3_54)),
% 0.21/0.48    inference(subsumption_resolution,[],[f640,f561])).
% 0.21/0.48  fof(f561,plain,(
% 0.21/0.48    v2_funct_1(k4_relat_1(sK2)) | ~spl3_53),
% 0.21/0.48    inference(avatar_component_clause,[],[f559])).
% 0.21/0.48  fof(f640,plain,(
% 0.21/0.48    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | (~spl3_22 | ~spl3_29 | ~spl3_37 | ~spl3_48 | ~spl3_54)),
% 0.21/0.48    inference(subsumption_resolution,[],[f639,f570])).
% 0.21/0.48  fof(f570,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~spl3_54),
% 0.21/0.48    inference(avatar_component_clause,[],[f568])).
% 0.21/0.48  fof(f639,plain,(
% 0.21/0.48    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | (~spl3_22 | ~spl3_29 | ~spl3_37 | ~spl3_48)),
% 0.21/0.48    inference(subsumption_resolution,[],[f427,f533])).
% 0.21/0.48  fof(f533,plain,(
% 0.21/0.48    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_48),
% 0.21/0.48    inference(avatar_component_clause,[],[f531])).
% 0.21/0.48  fof(f427,plain,(
% 0.21/0.48    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | (~spl3_22 | ~spl3_29 | ~spl3_37)),
% 0.21/0.48    inference(forward_demodulation,[],[f426,f246])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    sK2 = k2_funct_1(k4_relat_1(sK2)) | ~spl3_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f244])).
% 0.21/0.48  fof(f426,plain,(
% 0.21/0.48    ~v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | k2_funct_1(k4_relat_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | (~spl3_29 | ~spl3_37)),
% 0.21/0.48    inference(subsumption_resolution,[],[f417,f314])).
% 0.21/0.48  fof(f314,plain,(
% 0.21/0.48    v1_funct_1(k4_relat_1(sK2)) | ~spl3_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f312])).
% 0.21/0.48  fof(f417,plain,(
% 0.21/0.48    ~v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | k2_funct_1(k4_relat_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~spl3_37),
% 0.21/0.48    inference(resolution,[],[f401,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f47])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.48  fof(f401,plain,(
% 0.21/0.48    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_37),
% 0.21/0.48    inference(avatar_component_clause,[],[f399])).
% 0.21/0.48  fof(f586,plain,(
% 0.21/0.48    k2_relat_1(k4_relat_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f566,plain,(
% 0.21/0.48    ~spl3_20 | spl3_52),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f565])).
% 0.21/0.48  fof(f565,plain,(
% 0.21/0.48    $false | (~spl3_20 | spl3_52)),
% 0.21/0.48    inference(subsumption_resolution,[],[f564,f226])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl3_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f225])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    spl3_20 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.48  fof(f564,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl3_52),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f563])).
% 0.21/0.48  fof(f563,plain,(
% 0.21/0.48    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | spl3_52),
% 0.21/0.48    inference(superposition,[],[f557,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.48  fof(f557,plain,(
% 0.21/0.48    k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | spl3_52),
% 0.21/0.48    inference(avatar_component_clause,[],[f555])).
% 0.21/0.48  fof(f555,plain,(
% 0.21/0.48    spl3_52 <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.21/0.48  fof(f562,plain,(
% 0.21/0.48    ~spl3_52 | spl3_53 | ~spl3_1 | ~spl3_2 | ~spl3_20 | ~spl3_21 | ~spl3_27 | ~spl3_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f349,f312,f285,f239,f225,f93,f88,f559,f555])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    spl3_21 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    spl3_27 <=> v1_relat_1(k4_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.48  fof(f349,plain,(
% 0.21/0.48    v2_funct_1(k4_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_20 | ~spl3_21 | ~spl3_27 | ~spl3_29)),
% 0.21/0.48    inference(forward_demodulation,[],[f348,f241])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl3_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f239])).
% 0.21/0.48  fof(f348,plain,(
% 0.21/0.48    k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_20 | ~spl3_21 | ~spl3_27 | ~spl3_29)),
% 0.21/0.48    inference(forward_demodulation,[],[f347,f241])).
% 0.21/0.48  fof(f347,plain,(
% 0.21/0.48    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_20 | ~spl3_21 | ~spl3_27 | ~spl3_29)),
% 0.21/0.48    inference(subsumption_resolution,[],[f346,f287])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    v1_relat_1(k4_relat_1(sK2)) | ~spl3_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f285])).
% 0.21/0.48  fof(f346,plain,(
% 0.21/0.48    ~v1_relat_1(k4_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_20 | ~spl3_21 | ~spl3_29)),
% 0.21/0.48    inference(forward_demodulation,[],[f345,f241])).
% 0.21/0.48  fof(f345,plain,(
% 0.21/0.48    ~v1_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_20 | ~spl3_21 | ~spl3_29)),
% 0.21/0.48    inference(subsumption_resolution,[],[f344,f314])).
% 0.21/0.48  % (6538)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  fof(f344,plain,(
% 0.21/0.48    ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_20 | ~spl3_21)),
% 0.21/0.48    inference(forward_demodulation,[],[f343,f241])).
% 0.21/0.48  fof(f343,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f342,f226])).
% 0.21/0.48  fof(f342,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f341,f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f93])).
% 0.21/0.48  fof(f341,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f340,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f340,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f339,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.48  fof(f339,plain,(
% 0.21/0.48    ~v2_funct_1(k6_relat_1(k2_relat_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_20)),
% 0.21/0.48    inference(superposition,[],[f333,f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.48  fof(f333,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(k5_relat_1(X0,sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != k1_relat_1(sK2) | v2_funct_1(X0)) ) | (~spl3_1 | ~spl3_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f226])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK2)) | k2_relat_1(X0) != k1_relat_1(sK2) | v2_funct_1(X0)) ) | ~spl3_1),
% 0.21/0.48    inference(resolution,[],[f90,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 0.21/0.48  fof(f553,plain,(
% 0.21/0.48    spl3_51 | ~spl3_37),
% 0.21/0.48    inference(avatar_split_clause,[],[f411,f399,f550])).
% 0.21/0.48  fof(f550,plain,(
% 0.21/0.48    spl3_51 <=> k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.21/0.48  fof(f411,plain,(
% 0.21/0.48    k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~spl3_37),
% 0.21/0.48    inference(resolution,[],[f401,f78])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f534,plain,(
% 0.21/0.48    spl3_48 | ~spl3_33 | ~spl3_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f393,f367,f362,f531])).
% 0.21/0.48  fof(f362,plain,(
% 0.21/0.48    spl3_33 <=> v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.48  fof(f367,plain,(
% 0.21/0.48    spl3_34 <=> k1_relat_1(sK2) = k2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.48  fof(f393,plain,(
% 0.21/0.48    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_33 | ~spl3_34)),
% 0.21/0.48    inference(superposition,[],[f364,f369])).
% 0.21/0.48  fof(f369,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k2_struct_0(sK0) | ~spl3_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f367])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_33),
% 0.21/0.48    inference(avatar_component_clause,[],[f362])).
% 0.21/0.48  fof(f527,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_42 | ~spl3_46 | ~spl3_47),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f526])).
% 0.21/0.48  fof(f526,plain,(
% 0.21/0.48    $false | (~spl3_1 | ~spl3_42 | ~spl3_46 | ~spl3_47)),
% 0.21/0.48    inference(subsumption_resolution,[],[f525,f492])).
% 0.21/0.48  fof(f492,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_46),
% 0.21/0.48    inference(avatar_component_clause,[],[f490])).
% 0.21/0.48  fof(f490,plain,(
% 0.21/0.48    spl3_46 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.48  fof(f525,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_42 | ~spl3_47)),
% 0.21/0.48    inference(subsumption_resolution,[],[f524,f90])).
% 0.21/0.48  fof(f524,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_42 | ~spl3_47)),
% 0.21/0.48    inference(resolution,[],[f497,f461])).
% 0.21/0.48  fof(f461,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))) ) | ~spl3_42),
% 0.21/0.48    inference(avatar_component_clause,[],[f460])).
% 0.21/0.48  fof(f460,plain,(
% 0.21/0.48    spl3_42 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.48  fof(f497,plain,(
% 0.21/0.48    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_47),
% 0.21/0.48    inference(avatar_component_clause,[],[f495])).
% 0.21/0.48  fof(f495,plain,(
% 0.21/0.48    spl3_47 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.48  fof(f498,plain,(
% 0.21/0.48    spl3_47 | ~spl3_31 | ~spl3_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f392,f367,f321,f495])).
% 0.21/0.48  fof(f321,plain,(
% 0.21/0.48    spl3_31 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.48  fof(f392,plain,(
% 0.21/0.48    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_31 | ~spl3_34)),
% 0.21/0.48    inference(superposition,[],[f322,f369])).
% 0.21/0.48  fof(f322,plain,(
% 0.21/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_31),
% 0.21/0.48    inference(avatar_component_clause,[],[f321])).
% 0.21/0.48  fof(f493,plain,(
% 0.21/0.48    spl3_46 | ~spl3_13 | ~spl3_26 | ~spl3_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f487,f367,f277,f168,f490])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    spl3_26 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.48  fof(f487,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_26 | ~spl3_34)),
% 0.21/0.48    inference(forward_demodulation,[],[f302,f369])).
% 0.21/0.48  fof(f302,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_26)),
% 0.21/0.48    inference(superposition,[],[f170,f279])).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f277])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f168])).
% 0.21/0.48  fof(f466,plain,(
% 0.21/0.48    spl3_42 | spl3_43 | ~spl3_1 | ~spl3_13 | ~spl3_26 | ~spl3_31 | ~spl3_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f458,f367,f321,f277,f168,f88,f463,f460])).
% 0.21/0.48  fof(f463,plain,(
% 0.21/0.48    spl3_43 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.48  fof(f458,plain,(
% 0.21/0.48    ( ! [X0] : (r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0)) ) | (~spl3_1 | ~spl3_13 | ~spl3_26 | ~spl3_31 | ~spl3_34)),
% 0.21/0.48    inference(forward_demodulation,[],[f457,f369])).
% 0.21/0.48  fof(f457,plain,(
% 0.21/0.48    ( ! [X0] : (r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0)) ) | (~spl3_1 | ~spl3_13 | ~spl3_26 | ~spl3_31 | ~spl3_34)),
% 0.21/0.48    inference(forward_demodulation,[],[f456,f279])).
% 0.21/0.48  fof(f456,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_26 | ~spl3_31 | ~spl3_34)),
% 0.21/0.48    inference(forward_demodulation,[],[f455,f369])).
% 0.21/0.48  fof(f455,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_26 | ~spl3_31 | ~spl3_34)),
% 0.21/0.48    inference(forward_demodulation,[],[f454,f279])).
% 0.21/0.48  fof(f454,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_26 | ~spl3_31 | ~spl3_34)),
% 0.21/0.48    inference(forward_demodulation,[],[f453,f369])).
% 0.21/0.48  fof(f453,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(forward_demodulation,[],[f452,f279])).
% 0.21/0.48  fof(f452,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(subsumption_resolution,[],[f451,f322])).
% 0.21/0.48  fof(f451,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_26)),
% 0.21/0.48    inference(forward_demodulation,[],[f200,f279])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f189,f90])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | ~spl3_13),
% 0.21/0.48    inference(resolution,[],[f170,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.21/0.48  fof(f445,plain,(
% 0.21/0.48    spl3_40 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_23 | ~spl3_26 | ~spl3_31 | ~spl3_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f435,f367,f321,f277,f263,f239,f168,f93,f88,f442])).
% 0.21/0.48  fof(f442,plain,(
% 0.21/0.48    spl3_40 <=> k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    spl3_23 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.48  fof(f435,plain,(
% 0.21/0.48    k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_23 | ~spl3_26 | ~spl3_31 | ~spl3_34)),
% 0.21/0.48    inference(forward_demodulation,[],[f434,f241])).
% 0.21/0.48  fof(f434,plain,(
% 0.21/0.48    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_23 | ~spl3_26 | ~spl3_31 | ~spl3_34)),
% 0.21/0.48    inference(forward_demodulation,[],[f433,f369])).
% 0.21/0.48  fof(f433,plain,(
% 0.21/0.48    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_23 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(forward_demodulation,[],[f432,f279])).
% 0.21/0.48  fof(f432,plain,(
% 0.21/0.48    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_23 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(subsumption_resolution,[],[f431,f279])).
% 0.21/0.48  fof(f431,plain,(
% 0.21/0.48    k2_struct_0(sK1) != k2_relat_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_23 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(forward_demodulation,[],[f430,f265])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f263])).
% 0.21/0.48  fof(f430,plain,(
% 0.21/0.48    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(subsumption_resolution,[],[f429,f322])).
% 0.21/0.48  fof(f429,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_26)),
% 0.21/0.48    inference(forward_demodulation,[],[f199,f279])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f198,f95])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f188,f90])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.21/0.48    inference(resolution,[],[f170,f84])).
% 0.21/0.48  fof(f402,plain,(
% 0.21/0.48    spl3_37 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_23 | ~spl3_26 | ~spl3_31 | ~spl3_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f397,f367,f321,f277,f263,f239,f168,f93,f88,f399])).
% 0.21/0.48  fof(f397,plain,(
% 0.21/0.48    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_23 | ~spl3_26 | ~spl3_31 | ~spl3_34)),
% 0.21/0.48    inference(forward_demodulation,[],[f384,f369])).
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_23 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(forward_demodulation,[],[f383,f241])).
% 0.21/0.48  fof(f383,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_23 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(forward_demodulation,[],[f382,f279])).
% 0.21/0.48  fof(f382,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_23 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(subsumption_resolution,[],[f381,f279])).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    k2_struct_0(sK1) != k2_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_23 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(forward_demodulation,[],[f380,f265])).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(subsumption_resolution,[],[f379,f322])).
% 0.21/0.48  fof(f379,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_26)),
% 0.21/0.48    inference(forward_demodulation,[],[f197,f279])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f196,f95])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f187,f90])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl3_13),
% 0.21/0.48    inference(resolution,[],[f170,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.48  fof(f370,plain,(
% 0.21/0.48    spl3_34 | ~spl3_17 | ~spl3_20 | ~spl3_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f332,f317,f225,f210,f367])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    spl3_17 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.48  fof(f317,plain,(
% 0.21/0.48    spl3_30 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.48  fof(f332,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k2_struct_0(sK0) | (~spl3_17 | ~spl3_20 | ~spl3_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f331,f226])).
% 0.21/0.48  fof(f331,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k2_struct_0(sK0) | ~v1_relat_1(sK2) | (~spl3_17 | ~spl3_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f330,f212])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f210])).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k1_relat_1(sK2) = k2_struct_0(sK0) | ~v1_relat_1(sK2) | ~spl3_30),
% 0.21/0.48    inference(resolution,[],[f319,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f317])).
% 0.21/0.48  fof(f365,plain,(
% 0.21/0.48    spl3_33 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_23 | ~spl3_26 | ~spl3_31),
% 0.21/0.48    inference(avatar_split_clause,[],[f360,f321,f277,f263,f239,f168,f93,f88,f362])).
% 0.21/0.48  fof(f360,plain,(
% 0.21/0.48    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_23 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(forward_demodulation,[],[f359,f241])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_23 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(forward_demodulation,[],[f358,f279])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_23 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(subsumption_resolution,[],[f357,f279])).
% 0.21/0.48  fof(f357,plain,(
% 0.21/0.48    k2_struct_0(sK1) != k2_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_23 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(forward_demodulation,[],[f356,f265])).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_26 | ~spl3_31)),
% 0.21/0.48    inference(subsumption_resolution,[],[f355,f322])).
% 0.21/0.48  fof(f355,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_26)),
% 0.21/0.48    inference(forward_demodulation,[],[f195,f279])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f194,f95])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f186,f90])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~spl3_13),
% 0.21/0.48    inference(resolution,[],[f170,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f45])).
% 0.21/0.48  fof(f325,plain,(
% 0.21/0.48    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | u1_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    spl3_30 | ~spl3_31 | ~spl3_1 | spl3_12 | ~spl3_13 | ~spl3_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f310,f277,f168,f161,f88,f321,f317])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl3_12 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f310,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | spl3_12 | ~spl3_13 | ~spl3_26)),
% 0.21/0.48    inference(forward_demodulation,[],[f191,f279])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | spl3_12 | ~spl3_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f190,f90])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (spl3_12 | ~spl3_13)),
% 0.21/0.48    inference(subsumption_resolution,[],[f181,f163])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f161])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.21/0.48    inference(resolution,[],[f170,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(flattening,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.48  fof(f315,plain,(
% 0.21/0.48    spl3_29 | ~spl3_1 | ~spl3_20 | ~spl3_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f261,f239,f225,f88,f312])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    v1_funct_1(k4_relat_1(sK2)) | (~spl3_1 | ~spl3_20 | ~spl3_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f260,f226])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f251,f90])).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_21),
% 0.21/0.48    inference(superposition,[],[f67,f241])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f288,plain,(
% 0.21/0.48    spl3_27 | ~spl3_1 | ~spl3_20 | ~spl3_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f259,f239,f225,f88,f285])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    v1_relat_1(k4_relat_1(sK2)) | (~spl3_1 | ~spl3_20 | ~spl3_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f258,f226])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f250,f90])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    v1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_21),
% 0.21/0.48    inference(superposition,[],[f66,f241])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    k2_funct_1(sK2) != k4_relat_1(sK2) | sK2 != k2_funct_1(k2_funct_1(sK2)) | sK2 = k2_funct_1(k4_relat_1(sK2))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    spl3_23 | ~spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f182,f168,f263])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_13),
% 0.21/0.48    inference(resolution,[],[f170,f78])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    spl3_21 | ~spl3_1 | ~spl3_2 | ~spl3_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f237,f225,f93,f88,f239])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    k2_funct_1(sK2) = k4_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f226])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f90])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f95,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~spl3_13 | spl3_20),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f231])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    $false | (~spl3_13 | spl3_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f230,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_13 | spl3_20)),
% 0.21/0.48    inference(resolution,[],[f229,f170])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_20),
% 0.21/0.48    inference(resolution,[],[f227,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl3_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f225])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    spl3_19 | ~spl3_20 | ~spl3_1 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f116,f93,f88,f225,f221])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    spl3_19 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f90])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.48    inference(resolution,[],[f95,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    spl3_17 | ~spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f183,f168,f210])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.21/0.48    inference(resolution,[],[f170,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    ~spl3_16 | ~spl3_7 | ~spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f203,f136,f126,f205])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    spl3_16 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    spl3_7 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_7 | ~spl3_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f202,f138])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f136])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~spl3_7),
% 0.21/0.48    inference(forward_demodulation,[],[f55,f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f126])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f19])).
% 0.21/0.48  fof(f19,conjecture,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    spl3_13 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f159,f136,f131,f126,f168])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f153,f138])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8)),
% 0.21/0.48    inference(forward_demodulation,[],[f133,f128])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f131])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ~spl3_12 | spl3_3 | ~spl3_4 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f152,f126,f103,f98,f161])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl3_3 <=> v2_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl3_4 <=> l1_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    ~v1_xboole_0(k2_struct_0(sK1)) | (spl3_3 | ~spl3_4 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f151,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ~v2_struct_0(sK1) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f98])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f150,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    l1_struct_0(sK1) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_7),
% 0.21/0.48    inference(superposition,[],[f65,f128])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f53,f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl3_10 <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl3_9 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f119,f108,f136])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl3_5 <=> l1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.21/0.48    inference(resolution,[],[f110,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    l1_struct_0(sK0) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f108])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f52,f131])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl3_7 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f118,f103,f126])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_4),
% 0.21/0.48    inference(resolution,[],[f105,f61])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f51,f121])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f58,f108])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    l1_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f57,f103])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    l1_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f56,f98])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ~v2_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f54,f93])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    v2_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f50,f88])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (6536)------------------------------
% 0.21/0.48  % (6536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6536)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (6536)Memory used [KB]: 11001
% 0.21/0.48  % (6536)Time elapsed: 0.059 s
% 0.21/0.48  % (6536)------------------------------
% 0.21/0.48  % (6536)------------------------------
% 0.21/0.48  % (6535)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (6532)Success in time 0.123 s
%------------------------------------------------------------------------------
