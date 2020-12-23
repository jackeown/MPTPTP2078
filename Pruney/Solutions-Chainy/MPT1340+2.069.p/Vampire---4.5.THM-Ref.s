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
% DateTime   : Thu Dec  3 13:14:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  303 ( 586 expanded)
%              Number of leaves         :   65 ( 243 expanded)
%              Depth                    :   13
%              Number of atoms          : 1228 (2086 expanded)
%              Number of equality atoms :  193 ( 330 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f879,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f117,f122,f127,f132,f137,f154,f160,f187,f199,f204,f225,f227,f228,f262,f270,f275,f301,f326,f329,f338,f374,f377,f426,f457,f462,f479,f527,f538,f570,f582,f587,f634,f646,f690,f870,f876,f877,f878])).

fof(f878,plain,
    ( k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_funct_1(k2_funct_1(sK2)) != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | sK2 != k2_funct_1(k2_funct_1(sK2))
    | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),k2_funct_1(k2_funct_1(sK2)))
    | ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f877,plain,
    ( k1_relat_1(sK2) != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_funct_1(k2_funct_1(sK2)) != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | sK2 != k2_funct_1(k2_funct_1(sK2))
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),k2_funct_1(k2_funct_1(sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f876,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_31
    | spl3_84 ),
    inference(avatar_contradiction_clause,[],[f875])).

fof(f875,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_31
    | spl3_84 ),
    inference(subsumption_resolution,[],[f874,f309])).

fof(f309,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl3_31
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f874,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_84 ),
    inference(subsumption_resolution,[],[f873,f92])).

fof(f92,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f873,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_84 ),
    inference(subsumption_resolution,[],[f872,f87])).

fof(f87,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f872,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_84 ),
    inference(trivial_inequality_removal,[],[f871])).

fof(f871,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_84 ),
    inference(superposition,[],[f869,f66])).

fof(f66,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f869,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))
    | spl3_84 ),
    inference(avatar_component_clause,[],[f867])).

fof(f867,plain,
    ( spl3_84
  <=> k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f870,plain,
    ( spl3_83
    | ~ spl3_84
    | ~ spl3_1
    | ~ spl3_31
    | ~ spl3_48
    | ~ spl3_52
    | ~ spl3_53
    | ~ spl3_59
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f743,f631,f576,f510,f506,f469,f308,f85,f867,f863])).

fof(f863,plain,
    ( spl3_83
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f469,plain,
    ( spl3_48
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f506,plain,
    ( spl3_52
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f510,plain,
    ( spl3_53
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f576,plain,
    ( spl3_59
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f631,plain,
    ( spl3_62
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f743,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_31
    | ~ spl3_48
    | ~ spl3_52
    | ~ spl3_53
    | ~ spl3_59
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f742,f87])).

fof(f742,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_31
    | ~ spl3_48
    | ~ spl3_52
    | ~ spl3_53
    | ~ spl3_59
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f737,f309])).

fof(f737,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_48
    | ~ spl3_52
    | ~ spl3_53
    | ~ spl3_59
    | ~ spl3_62 ),
    inference(equality_resolution,[],[f734])).

fof(f734,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != k2_relat_1(sK2)
        | k5_relat_1(X0,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_funct_1(k2_funct_1(sK2)) = X0 )
    | ~ spl3_48
    | ~ spl3_52
    | ~ spl3_53
    | ~ spl3_59
    | ~ spl3_62 ),
    inference(forward_demodulation,[],[f650,f632])).

fof(f632,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f631])).

fof(f650,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK2))
        | k2_funct_1(k2_funct_1(sK2)) = X0 )
    | ~ spl3_48
    | ~ spl3_52
    | ~ spl3_53
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f649,f511])).

fof(f511,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f510])).

fof(f649,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK2))
        | k5_relat_1(X0,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
        | k2_funct_1(k2_funct_1(sK2)) = X0 )
    | ~ spl3_48
    | ~ spl3_52
    | ~ spl3_59 ),
    inference(subsumption_resolution,[],[f648,f577])).

fof(f577,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f576])).

fof(f648,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK2))
        | k5_relat_1(X0,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
        | k2_funct_1(k2_funct_1(sK2)) = X0 )
    | ~ spl3_48
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f647,f470])).

fof(f470,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f469])).

fof(f647,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK2))
        | k5_relat_1(X0,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
        | k2_funct_1(k2_funct_1(sK2)) = X0 )
    | ~ spl3_52 ),
    inference(resolution,[],[f507,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f507,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f506])).

fof(f690,plain,
    ( spl3_65
    | ~ spl3_25
    | ~ spl3_27
    | ~ spl3_35
    | ~ spl3_48
    | ~ spl3_52
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f680,f529,f506,f469,f335,f272,f259,f687])).

fof(f687,plain,
    ( spl3_65
  <=> k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f259,plain,
    ( spl3_25
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f272,plain,
    ( spl3_27
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f335,plain,
    ( spl3_35
  <=> k1_relat_1(sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f529,plain,
    ( spl3_55
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f680,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_25
    | ~ spl3_27
    | ~ spl3_35
    | ~ spl3_48
    | ~ spl3_52
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f600,f507])).

fof(f600,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_25
    | ~ spl3_27
    | ~ spl3_35
    | ~ spl3_48
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f599,f337])).

fof(f337,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f335])).

fof(f599,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_25
    | ~ spl3_27
    | ~ spl3_35
    | ~ spl3_48
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f598,f531])).

fof(f531,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f529])).

fof(f598,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_25
    | ~ spl3_27
    | ~ spl3_35
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f597,f337])).

fof(f597,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_25
    | ~ spl3_27
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f287,f470])).

fof(f287,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f282,f261])).

fof(f261,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f259])).

fof(f282,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_27 ),
    inference(resolution,[],[f274,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f274,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f272])).

fof(f646,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_31
    | spl3_62 ),
    inference(avatar_contradiction_clause,[],[f645])).

fof(f645,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_31
    | spl3_62 ),
    inference(subsumption_resolution,[],[f644,f309])).

fof(f644,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_62 ),
    inference(subsumption_resolution,[],[f643,f92])).

fof(f643,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_62 ),
    inference(subsumption_resolution,[],[f642,f87])).

fof(f642,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_62 ),
    inference(trivial_inequality_removal,[],[f641])).

fof(f641,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_62 ),
    inference(superposition,[],[f633,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f633,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | spl3_62 ),
    inference(avatar_component_clause,[],[f631])).

fof(f634,plain,
    ( ~ spl3_62
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_31
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f629,f580,f308,f90,f85,f631])).

fof(f580,plain,
    ( spl3_60
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2)))
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f629,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_31
    | ~ spl3_60 ),
    inference(subsumption_resolution,[],[f628,f92])).

fof(f628,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_31
    | ~ spl3_60 ),
    inference(subsumption_resolution,[],[f627,f87])).

fof(f627,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl3_31
    | ~ spl3_60 ),
    inference(subsumption_resolution,[],[f626,f309])).

fof(f626,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl3_60 ),
    inference(subsumption_resolution,[],[f625,f58])).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f625,plain,
    ( ~ v2_funct_1(k6_relat_1(k1_relat_1(sK2)))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl3_60 ),
    inference(duplicate_literal_removal,[],[f624])).

fof(f624,plain,
    ( ~ v2_funct_1(k6_relat_1(k1_relat_1(sK2)))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_60 ),
    inference(superposition,[],[f581,f66])).

fof(f581,plain,
    ( ! [X1] :
        ( ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2)))
        | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1) )
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f580])).

fof(f587,plain,
    ( ~ spl3_1
    | ~ spl3_31
    | spl3_59 ),
    inference(avatar_contradiction_clause,[],[f586])).

fof(f586,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_31
    | spl3_59 ),
    inference(subsumption_resolution,[],[f585,f309])).

fof(f585,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_59 ),
    inference(subsumption_resolution,[],[f583,f87])).

fof(f583,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_59 ),
    inference(resolution,[],[f578,f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f578,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_59 ),
    inference(avatar_component_clause,[],[f576])).

fof(f582,plain,
    ( ~ spl3_59
    | spl3_60
    | ~ spl3_48
    | spl3_52 ),
    inference(avatar_split_clause,[],[f521,f506,f469,f580,f576])).

fof(f521,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2)))
        | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_48
    | spl3_52 ),
    inference(subsumption_resolution,[],[f519,f470])).

fof(f519,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2)))
        | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | spl3_52 ),
    inference(resolution,[],[f508,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f508,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f506])).

fof(f570,plain,
    ( ~ spl3_1
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_42
    | ~ spl3_46 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_42
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f568,f425])).

fof(f425,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl3_42
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f568,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f567,f87])).

fof(f567,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_46 ),
    inference(resolution,[],[f398,f461])).

fof(f461,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl3_46
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f398,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) )
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(superposition,[],[f321,f337])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl3_33
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f538,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f527,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_31
    | spl3_53 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_31
    | spl3_53 ),
    inference(subsumption_resolution,[],[f525,f309])).

fof(f525,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_53 ),
    inference(subsumption_resolution,[],[f524,f92])).

fof(f524,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_53 ),
    inference(subsumption_resolution,[],[f523,f87])).

fof(f523,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_53 ),
    inference(trivial_inequality_removal,[],[f522])).

fof(f522,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_53 ),
    inference(superposition,[],[f512,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f512,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | spl3_53 ),
    inference(avatar_component_clause,[],[f510])).

fof(f479,plain,
    ( ~ spl3_1
    | ~ spl3_31
    | spl3_48 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_31
    | spl3_48 ),
    inference(subsumption_resolution,[],[f477,f309])).

fof(f477,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_48 ),
    inference(subsumption_resolution,[],[f474,f87])).

fof(f474,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_48 ),
    inference(resolution,[],[f471,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f471,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_48 ),
    inference(avatar_component_clause,[],[f469])).

fof(f462,plain,
    ( spl3_46
    | ~ spl3_26
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f394,f335,f267,f459])).

fof(f267,plain,
    ( spl3_26
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f394,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_26
    | ~ spl3_35 ),
    inference(superposition,[],[f269,f337])).

fof(f269,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f267])).

fof(f457,plain,
    ( spl3_45
    | ~ spl3_27
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f451,f335,f272,f454])).

fof(f454,plain,
    ( spl3_45
  <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f451,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_27
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f277,f337])).

fof(f277,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_27 ),
    inference(resolution,[],[f274,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f426,plain,
    ( spl3_42
    | ~ spl3_13
    | ~ spl3_20
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f416,f335,f214,f157,f423])).

fof(f157,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f214,plain,
    ( spl3_20
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f416,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_20
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f238,f337])).

fof(f238,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(superposition,[],[f159,f216])).

fof(f216,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f214])).

fof(f159,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f157])).

fof(f377,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | spl3_3
    | ~ spl3_4
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f242,f245])).

fof(f245,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl3_23
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f242,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f241,f97])).

fof(f97,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f241,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f240,f102])).

fof(f102,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f240,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_20 ),
    inference(superposition,[],[f61,f216])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f374,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f338,plain,
    ( spl3_35
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f330,f308,f218,f184,f335])).

fof(f184,plain,
    ( spl3_14
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f218,plain,
    ( spl3_21
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f330,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f230,f309])).

fof(f230,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f229,f186])).

fof(f186,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f184])).

fof(f229,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(resolution,[],[f220,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f220,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f218])).

fof(f329,plain,
    ( ~ spl3_13
    | spl3_31 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl3_13
    | spl3_31 ),
    inference(subsumption_resolution,[],[f327,f71])).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f327,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_13
    | spl3_31 ),
    inference(resolution,[],[f315,f159])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_31 ),
    inference(resolution,[],[f310,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f310,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_31 ),
    inference(avatar_component_clause,[],[f308])).

fof(f326,plain,
    ( spl3_33
    | spl3_34
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f318,f214,f157,f151,f85,f323,f320])).

fof(f323,plain,
    ( spl3_34
  <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f151,plain,
    ( spl3_12
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f318,plain,
    ( ! [X0] :
        ( r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0) )
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f317,f216])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f316,f216])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f181,f216])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f180,f87])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f168,f153])).

fof(f153,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f168,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_13 ),
    inference(resolution,[],[f159,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f301,plain,
    ( spl3_29
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f296,f214,f210,f157,f151,f90,f85,f298])).

fof(f298,plain,
    ( spl3_29
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f210,plain,
    ( spl3_19
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f296,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f295,f216])).

fof(f295,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f294,f212])).

fof(f212,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f210])).

fof(f294,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f179,f216])).

fof(f179,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f178,f92])).

fof(f178,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f177,f87])).

fof(f177,plain,
    ( ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f167,f153])).

fof(f167,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f159,f81])).

fof(f275,plain,
    ( spl3_27
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f265,f214,f210,f157,f151,f90,f85,f272])).

fof(f265,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f264,f216])).

fof(f264,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f263,f212])).

fof(f263,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f176,f216])).

fof(f176,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f175,f92])).

fof(f175,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f174,f87])).

fof(f174,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f166,f153])).

fof(f166,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_13 ),
    inference(resolution,[],[f159,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f270,plain,
    ( spl3_26
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f239,f214,f151,f267])).

fof(f239,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(superposition,[],[f153,f216])).

fof(f262,plain,
    ( spl3_25
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f257,f214,f210,f157,f151,f90,f85,f259])).

fof(f257,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f256,f216])).

fof(f256,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f255,f212])).

fof(f255,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f173,f216])).

fof(f173,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f172,f92])).

fof(f172,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f171,f87])).

fof(f171,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f165,f153])).

fof(f165,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f159,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f228,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f227,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f225,plain,
    ( spl3_21
    | spl3_22
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f170,f157,f151,f85,f222,f218])).

fof(f222,plain,
    ( spl3_22
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f170,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f169,f153])).

fof(f169,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f161,f87])).

fof(f161,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f159,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f204,plain,
    ( spl3_17
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f162,f157,f201])).

fof(f201,plain,
    ( spl3_17
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f162,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f159,f75])).

fof(f199,plain,
    ( ~ spl3_16
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f189,f129,f119,f196])).

fof(f196,plain,
    ( spl3_16
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f119,plain,
    ( spl3_7
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f129,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f189,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f188,f131])).

fof(f131,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f188,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f53,f121])).

fof(f121,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f53,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f187,plain,
    ( spl3_14
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f163,f157,f184])).

fof(f163,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f159,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f160,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f147,f129,f124,f119,f157])).

fof(f124,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f147,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f143,f131])).

fof(f143,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f126,f121])).

fof(f126,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f154,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f146,f129,f119,f114,f151])).

fof(f114,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f146,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f145,f121])).

fof(f145,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f116,f131])).

fof(f116,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f114])).

fof(f137,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f51,f134])).

fof(f134,plain,
    ( spl3_10
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f51,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f132,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f112,f105,f129])).

fof(f105,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f112,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f107,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f107,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f127,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f50,f124])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f122,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f111,f100,f119])).

fof(f111,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f102,f59])).

fof(f117,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f49,f114])).

fof(f49,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f108,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f56,f105])).

fof(f56,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f55,f100])).

fof(f55,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f54,f95])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f52,f90])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f88,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f48,f85])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:11:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.41  % (3583)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (3571)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (3571)Refutation not found, incomplete strategy% (3571)------------------------------
% 0.20/0.47  % (3571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (3571)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (3571)Memory used [KB]: 10746
% 0.20/0.47  % (3571)Time elapsed: 0.066 s
% 0.20/0.47  % (3571)------------------------------
% 0.20/0.47  % (3571)------------------------------
% 0.20/0.47  % (3578)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (3581)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (3584)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (3570)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (3573)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (3590)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (3576)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (3574)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (3590)Refutation not found, incomplete strategy% (3590)------------------------------
% 0.20/0.50  % (3590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3590)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3590)Memory used [KB]: 10618
% 0.20/0.50  % (3590)Time elapsed: 0.104 s
% 0.20/0.50  % (3590)------------------------------
% 0.20/0.50  % (3590)------------------------------
% 0.20/0.50  % (3575)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (3572)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (3580)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (3582)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (3577)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (3585)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (3579)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (3570)Refutation not found, incomplete strategy% (3570)------------------------------
% 0.20/0.51  % (3570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3570)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3570)Memory used [KB]: 6524
% 0.20/0.51  % (3570)Time elapsed: 0.097 s
% 0.20/0.51  % (3570)------------------------------
% 0.20/0.51  % (3570)------------------------------
% 0.20/0.51  % (3586)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (3589)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (3587)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (3573)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f879,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f117,f122,f127,f132,f137,f154,f160,f187,f199,f204,f225,f227,f228,f262,f270,f275,f301,f326,f329,f338,f374,f377,f426,f457,f462,f479,f527,f538,f570,f582,f587,f634,f646,f690,f870,f876,f877,f878])).
% 0.20/0.51  fof(f878,plain,(
% 0.20/0.51    k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_funct_1(k2_funct_1(sK2)) != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_struct_0(sK0) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | sK2 != k2_funct_1(k2_funct_1(sK2)) | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),k2_funct_1(k2_funct_1(sK2))) | ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f877,plain,(
% 0.20/0.51    k1_relat_1(sK2) != k2_struct_0(sK0) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_funct_1(k2_funct_1(sK2)) != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | sK2 != k2_funct_1(k2_funct_1(sK2)) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),k2_funct_1(k2_funct_1(sK2)))),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f876,plain,(
% 0.20/0.51    ~spl3_1 | ~spl3_2 | ~spl3_31 | spl3_84),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f875])).
% 0.20/0.51  fof(f875,plain,(
% 0.20/0.51    $false | (~spl3_1 | ~spl3_2 | ~spl3_31 | spl3_84)),
% 0.20/0.51    inference(subsumption_resolution,[],[f874,f309])).
% 0.20/0.51  fof(f309,plain,(
% 0.20/0.51    v1_relat_1(sK2) | ~spl3_31),
% 0.20/0.51    inference(avatar_component_clause,[],[f308])).
% 0.20/0.51  fof(f308,plain,(
% 0.20/0.51    spl3_31 <=> v1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.51  fof(f874,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | spl3_84)),
% 0.20/0.51    inference(subsumption_resolution,[],[f873,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    v2_funct_1(sK2) | ~spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl3_2 <=> v2_funct_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f873,plain,(
% 0.20/0.51    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_84)),
% 0.20/0.51    inference(subsumption_resolution,[],[f872,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    v1_funct_1(sK2) | ~spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f85])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl3_1 <=> v1_funct_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f872,plain,(
% 0.20/0.51    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_84),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f871])).
% 0.20/0.51  fof(f871,plain,(
% 0.20/0.51    k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_84),
% 0.20/0.51    inference(superposition,[],[f869,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.52  fof(f869,plain,(
% 0.20/0.52    k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) | spl3_84),
% 0.20/0.52    inference(avatar_component_clause,[],[f867])).
% 0.20/0.52  fof(f867,plain,(
% 0.20/0.52    spl3_84 <=> k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 0.20/0.52  fof(f870,plain,(
% 0.20/0.52    spl3_83 | ~spl3_84 | ~spl3_1 | ~spl3_31 | ~spl3_48 | ~spl3_52 | ~spl3_53 | ~spl3_59 | ~spl3_62),
% 0.20/0.52    inference(avatar_split_clause,[],[f743,f631,f576,f510,f506,f469,f308,f85,f867,f863])).
% 0.20/0.52  fof(f863,plain,(
% 0.20/0.52    spl3_83 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.20/0.52  fof(f469,plain,(
% 0.20/0.52    spl3_48 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.52  fof(f506,plain,(
% 0.20/0.52    spl3_52 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.20/0.52  fof(f510,plain,(
% 0.20/0.52    spl3_53 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.20/0.52  fof(f576,plain,(
% 0.20/0.52    spl3_59 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.20/0.52  fof(f631,plain,(
% 0.20/0.52    spl3_62 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.20/0.52  fof(f743,plain,(
% 0.20/0.52    k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_31 | ~spl3_48 | ~spl3_52 | ~spl3_53 | ~spl3_59 | ~spl3_62)),
% 0.20/0.52    inference(subsumption_resolution,[],[f742,f87])).
% 0.20/0.52  fof(f742,plain,(
% 0.20/0.52    k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_31 | ~spl3_48 | ~spl3_52 | ~spl3_53 | ~spl3_59 | ~spl3_62)),
% 0.20/0.52    inference(subsumption_resolution,[],[f737,f309])).
% 0.20/0.52  fof(f737,plain,(
% 0.20/0.52    k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_48 | ~spl3_52 | ~spl3_53 | ~spl3_59 | ~spl3_62)),
% 0.20/0.52    inference(equality_resolution,[],[f734])).
% 0.20/0.52  fof(f734,plain,(
% 0.20/0.52    ( ! [X0] : (k2_relat_1(X0) != k2_relat_1(sK2) | k5_relat_1(X0,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_funct_1(k2_funct_1(sK2)) = X0) ) | (~spl3_48 | ~spl3_52 | ~spl3_53 | ~spl3_59 | ~spl3_62)),
% 0.20/0.52    inference(forward_demodulation,[],[f650,f632])).
% 0.20/0.52  fof(f632,plain,(
% 0.20/0.52    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_62),
% 0.20/0.52    inference(avatar_component_clause,[],[f631])).
% 0.20/0.52  fof(f650,plain,(
% 0.20/0.52    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X0) ) | (~spl3_48 | ~spl3_52 | ~spl3_53 | ~spl3_59)),
% 0.20/0.52    inference(forward_demodulation,[],[f649,f511])).
% 0.20/0.52  fof(f511,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_53),
% 0.20/0.52    inference(avatar_component_clause,[],[f510])).
% 0.20/0.52  fof(f649,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK2)) | k5_relat_1(X0,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | k2_funct_1(k2_funct_1(sK2)) = X0) ) | (~spl3_48 | ~spl3_52 | ~spl3_59)),
% 0.20/0.52    inference(subsumption_resolution,[],[f648,f577])).
% 0.20/0.52  fof(f577,plain,(
% 0.20/0.52    v1_relat_1(k2_funct_1(sK2)) | ~spl3_59),
% 0.20/0.52    inference(avatar_component_clause,[],[f576])).
% 0.20/0.52  fof(f648,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK2)) | k5_relat_1(X0,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | k2_funct_1(k2_funct_1(sK2)) = X0) ) | (~spl3_48 | ~spl3_52)),
% 0.20/0.52    inference(subsumption_resolution,[],[f647,f470])).
% 0.20/0.52  fof(f470,plain,(
% 0.20/0.52    v1_funct_1(k2_funct_1(sK2)) | ~spl3_48),
% 0.20/0.52    inference(avatar_component_clause,[],[f469])).
% 0.20/0.52  fof(f647,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK2)) | k5_relat_1(X0,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | k2_funct_1(k2_funct_1(sK2)) = X0) ) | ~spl3_52),
% 0.20/0.52    inference(resolution,[],[f507,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.20/0.52  fof(f507,plain,(
% 0.20/0.52    v2_funct_1(k2_funct_1(sK2)) | ~spl3_52),
% 0.20/0.52    inference(avatar_component_clause,[],[f506])).
% 0.20/0.52  fof(f690,plain,(
% 0.20/0.52    spl3_65 | ~spl3_25 | ~spl3_27 | ~spl3_35 | ~spl3_48 | ~spl3_52 | ~spl3_55),
% 0.20/0.52    inference(avatar_split_clause,[],[f680,f529,f506,f469,f335,f272,f259,f687])).
% 0.20/0.52  fof(f687,plain,(
% 0.20/0.52    spl3_65 <=> k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 0.20/0.52  fof(f259,plain,(
% 0.20/0.52    spl3_25 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.52  fof(f272,plain,(
% 0.20/0.52    spl3_27 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.52  fof(f335,plain,(
% 0.20/0.52    spl3_35 <=> k1_relat_1(sK2) = k2_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.52  fof(f529,plain,(
% 0.20/0.52    spl3_55 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.20/0.52  fof(f680,plain,(
% 0.20/0.52    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_25 | ~spl3_27 | ~spl3_35 | ~spl3_48 | ~spl3_52 | ~spl3_55)),
% 0.20/0.52    inference(subsumption_resolution,[],[f600,f507])).
% 0.20/0.52  fof(f600,plain,(
% 0.20/0.52    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_25 | ~spl3_27 | ~spl3_35 | ~spl3_48 | ~spl3_55)),
% 0.20/0.52    inference(forward_demodulation,[],[f599,f337])).
% 0.20/0.52  fof(f337,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k2_struct_0(sK0) | ~spl3_35),
% 0.20/0.52    inference(avatar_component_clause,[],[f335])).
% 0.20/0.52  fof(f599,plain,(
% 0.20/0.52    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_25 | ~spl3_27 | ~spl3_35 | ~spl3_48 | ~spl3_55)),
% 0.20/0.52    inference(subsumption_resolution,[],[f598,f531])).
% 0.20/0.52  fof(f531,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_55),
% 0.20/0.52    inference(avatar_component_clause,[],[f529])).
% 0.20/0.52  fof(f598,plain,(
% 0.20/0.52    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_25 | ~spl3_27 | ~spl3_35 | ~spl3_48)),
% 0.20/0.52    inference(forward_demodulation,[],[f597,f337])).
% 0.20/0.52  fof(f597,plain,(
% 0.20/0.52    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_25 | ~spl3_27 | ~spl3_48)),
% 0.20/0.52    inference(subsumption_resolution,[],[f287,f470])).
% 0.20/0.52  fof(f287,plain,(
% 0.20/0.52    ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_25 | ~spl3_27)),
% 0.20/0.52    inference(subsumption_resolution,[],[f282,f261])).
% 0.20/0.52  fof(f261,plain,(
% 0.20/0.52    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_25),
% 0.20/0.52    inference(avatar_component_clause,[],[f259])).
% 0.20/0.52  fof(f282,plain,(
% 0.20/0.52    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_27),
% 0.20/0.52    inference(resolution,[],[f274,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.52  fof(f274,plain,(
% 0.20/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_27),
% 0.20/0.52    inference(avatar_component_clause,[],[f272])).
% 0.20/0.52  fof(f646,plain,(
% 0.20/0.52    ~spl3_1 | ~spl3_2 | ~spl3_31 | spl3_62),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f645])).
% 0.20/0.52  fof(f645,plain,(
% 0.20/0.52    $false | (~spl3_1 | ~spl3_2 | ~spl3_31 | spl3_62)),
% 0.20/0.52    inference(subsumption_resolution,[],[f644,f309])).
% 0.20/0.52  fof(f644,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | spl3_62)),
% 0.20/0.52    inference(subsumption_resolution,[],[f643,f92])).
% 0.20/0.52  fof(f643,plain,(
% 0.20/0.52    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_62)),
% 0.20/0.52    inference(subsumption_resolution,[],[f642,f87])).
% 0.20/0.52  fof(f642,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_62),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f641])).
% 0.20/0.52  fof(f641,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_62),
% 0.20/0.52    inference(superposition,[],[f633,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.52  fof(f633,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | spl3_62),
% 0.20/0.52    inference(avatar_component_clause,[],[f631])).
% 0.20/0.52  fof(f634,plain,(
% 0.20/0.52    ~spl3_62 | ~spl3_1 | ~spl3_2 | ~spl3_31 | ~spl3_60),
% 0.20/0.52    inference(avatar_split_clause,[],[f629,f580,f308,f90,f85,f631])).
% 0.20/0.52  fof(f580,plain,(
% 0.20/0.52    spl3_60 <=> ! [X1] : (~v1_relat_1(X1) | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) | ~v1_funct_1(X1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.20/0.52  fof(f629,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_31 | ~spl3_60)),
% 0.20/0.52    inference(subsumption_resolution,[],[f628,f92])).
% 0.20/0.52  fof(f628,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | (~spl3_1 | ~spl3_31 | ~spl3_60)),
% 0.20/0.52    inference(subsumption_resolution,[],[f627,f87])).
% 0.20/0.52  fof(f627,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl3_31 | ~spl3_60)),
% 0.20/0.52    inference(subsumption_resolution,[],[f626,f309])).
% 0.20/0.52  fof(f626,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl3_60),
% 0.20/0.52    inference(subsumption_resolution,[],[f625,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.52  fof(f625,plain,(
% 0.20/0.52    ~v2_funct_1(k6_relat_1(k1_relat_1(sK2))) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl3_60),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f624])).
% 0.20/0.52  fof(f624,plain,(
% 0.20/0.52    ~v2_funct_1(k6_relat_1(k1_relat_1(sK2))) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_60),
% 0.20/0.52    inference(superposition,[],[f581,f66])).
% 0.20/0.52  fof(f581,plain,(
% 0.20/0.52    ( ! [X1] : (~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X1) | ~v1_funct_1(X1)) ) | ~spl3_60),
% 0.20/0.52    inference(avatar_component_clause,[],[f580])).
% 0.20/0.52  fof(f587,plain,(
% 0.20/0.52    ~spl3_1 | ~spl3_31 | spl3_59),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f586])).
% 0.20/0.52  fof(f586,plain,(
% 0.20/0.52    $false | (~spl3_1 | ~spl3_31 | spl3_59)),
% 0.20/0.52    inference(subsumption_resolution,[],[f585,f309])).
% 0.20/0.52  fof(f585,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | (~spl3_1 | spl3_59)),
% 0.20/0.52    inference(subsumption_resolution,[],[f583,f87])).
% 0.20/0.52  fof(f583,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_59),
% 0.20/0.52    inference(resolution,[],[f578,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.52  fof(f578,plain,(
% 0.20/0.52    ~v1_relat_1(k2_funct_1(sK2)) | spl3_59),
% 0.20/0.52    inference(avatar_component_clause,[],[f576])).
% 0.20/0.52  fof(f582,plain,(
% 0.20/0.52    ~spl3_59 | spl3_60 | ~spl3_48 | spl3_52),
% 0.20/0.52    inference(avatar_split_clause,[],[f521,f506,f469,f580,f576])).
% 0.20/0.52  fof(f521,plain,(
% 0.20/0.52    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_48 | spl3_52)),
% 0.20/0.52    inference(subsumption_resolution,[],[f519,f470])).
% 0.20/0.52  fof(f519,plain,(
% 0.20/0.52    ( ! [X1] : (~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,k2_funct_1(sK2))) | k2_relat_1(X1) != k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | spl3_52),
% 0.20/0.52    inference(resolution,[],[f508,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 0.20/0.52  fof(f508,plain,(
% 0.20/0.52    ~v2_funct_1(k2_funct_1(sK2)) | spl3_52),
% 0.20/0.52    inference(avatar_component_clause,[],[f506])).
% 0.20/0.52  fof(f570,plain,(
% 0.20/0.52    ~spl3_1 | ~spl3_33 | ~spl3_35 | ~spl3_42 | ~spl3_46),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f569])).
% 0.20/0.52  fof(f569,plain,(
% 0.20/0.52    $false | (~spl3_1 | ~spl3_33 | ~spl3_35 | ~spl3_42 | ~spl3_46)),
% 0.20/0.52    inference(subsumption_resolution,[],[f568,f425])).
% 0.20/0.52  fof(f425,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_42),
% 0.20/0.52    inference(avatar_component_clause,[],[f423])).
% 0.20/0.52  fof(f423,plain,(
% 0.20/0.52    spl3_42 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.52  fof(f568,plain,(
% 0.20/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_33 | ~spl3_35 | ~spl3_46)),
% 0.20/0.52    inference(subsumption_resolution,[],[f567,f87])).
% 0.20/0.52  fof(f567,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_33 | ~spl3_35 | ~spl3_46)),
% 0.20/0.52    inference(resolution,[],[f398,f461])).
% 0.20/0.52  fof(f461,plain,(
% 0.20/0.52    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_46),
% 0.20/0.52    inference(avatar_component_clause,[],[f459])).
% 0.20/0.52  fof(f459,plain,(
% 0.20/0.52    spl3_46 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.20/0.52  fof(f398,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))) ) | (~spl3_33 | ~spl3_35)),
% 0.20/0.52    inference(superposition,[],[f321,f337])).
% 0.20/0.52  fof(f321,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))) ) | ~spl3_33),
% 0.20/0.52    inference(avatar_component_clause,[],[f320])).
% 0.20/0.52  fof(f320,plain,(
% 0.20/0.52    spl3_33 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.52  fof(f538,plain,(
% 0.20/0.52    k2_relat_1(k2_funct_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f527,plain,(
% 0.20/0.52    ~spl3_1 | ~spl3_2 | ~spl3_31 | spl3_53),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f526])).
% 0.20/0.52  fof(f526,plain,(
% 0.20/0.52    $false | (~spl3_1 | ~spl3_2 | ~spl3_31 | spl3_53)),
% 0.20/0.52    inference(subsumption_resolution,[],[f525,f309])).
% 0.20/0.52  fof(f525,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | spl3_53)),
% 0.20/0.52    inference(subsumption_resolution,[],[f524,f92])).
% 0.20/0.52  fof(f524,plain,(
% 0.20/0.52    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_53)),
% 0.20/0.52    inference(subsumption_resolution,[],[f523,f87])).
% 0.20/0.52  fof(f523,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_53),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f522])).
% 0.20/0.52  fof(f522,plain,(
% 0.20/0.52    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_53),
% 0.20/0.52    inference(superposition,[],[f512,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f512,plain,(
% 0.20/0.52    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | spl3_53),
% 0.20/0.52    inference(avatar_component_clause,[],[f510])).
% 0.20/0.52  fof(f479,plain,(
% 0.20/0.52    ~spl3_1 | ~spl3_31 | spl3_48),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f478])).
% 0.20/0.52  fof(f478,plain,(
% 0.20/0.52    $false | (~spl3_1 | ~spl3_31 | spl3_48)),
% 0.20/0.52    inference(subsumption_resolution,[],[f477,f309])).
% 0.20/0.52  fof(f477,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | (~spl3_1 | spl3_48)),
% 0.20/0.52    inference(subsumption_resolution,[],[f474,f87])).
% 0.20/0.52  fof(f474,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_48),
% 0.20/0.52    inference(resolution,[],[f471,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f471,plain,(
% 0.20/0.52    ~v1_funct_1(k2_funct_1(sK2)) | spl3_48),
% 0.20/0.52    inference(avatar_component_clause,[],[f469])).
% 0.20/0.52  fof(f462,plain,(
% 0.20/0.52    spl3_46 | ~spl3_26 | ~spl3_35),
% 0.20/0.52    inference(avatar_split_clause,[],[f394,f335,f267,f459])).
% 0.20/0.52  fof(f267,plain,(
% 0.20/0.52    spl3_26 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.52  fof(f394,plain,(
% 0.20/0.52    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_26 | ~spl3_35)),
% 0.20/0.52    inference(superposition,[],[f269,f337])).
% 0.20/0.52  fof(f269,plain,(
% 0.20/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_26),
% 0.20/0.52    inference(avatar_component_clause,[],[f267])).
% 0.20/0.52  fof(f457,plain,(
% 0.20/0.52    spl3_45 | ~spl3_27 | ~spl3_35),
% 0.20/0.52    inference(avatar_split_clause,[],[f451,f335,f272,f454])).
% 0.20/0.52  fof(f454,plain,(
% 0.20/0.52    spl3_45 <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.52  fof(f451,plain,(
% 0.20/0.52    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_27 | ~spl3_35)),
% 0.20/0.52    inference(forward_demodulation,[],[f277,f337])).
% 0.20/0.52  fof(f277,plain,(
% 0.20/0.52    k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_27),
% 0.20/0.52    inference(resolution,[],[f274,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.52  fof(f426,plain,(
% 0.20/0.52    spl3_42 | ~spl3_13 | ~spl3_20 | ~spl3_35),
% 0.20/0.52    inference(avatar_split_clause,[],[f416,f335,f214,f157,f423])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.52  fof(f214,plain,(
% 0.20/0.52    spl3_20 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.52  fof(f416,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_20 | ~spl3_35)),
% 0.20/0.52    inference(forward_demodulation,[],[f238,f337])).
% 0.20/0.52  fof(f238,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_20)),
% 0.20/0.52    inference(superposition,[],[f159,f216])).
% 0.20/0.52  fof(f216,plain,(
% 0.20/0.52    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_20),
% 0.20/0.52    inference(avatar_component_clause,[],[f214])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f157])).
% 0.20/0.52  fof(f377,plain,(
% 0.20/0.52    spl3_3 | ~spl3_4 | ~spl3_20 | ~spl3_23),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f376])).
% 0.20/0.52  fof(f376,plain,(
% 0.20/0.52    $false | (spl3_3 | ~spl3_4 | ~spl3_20 | ~spl3_23)),
% 0.20/0.52    inference(subsumption_resolution,[],[f242,f245])).
% 0.20/0.52  fof(f245,plain,(
% 0.20/0.52    v1_xboole_0(k2_relat_1(sK2)) | ~spl3_23),
% 0.20/0.52    inference(avatar_component_clause,[],[f244])).
% 0.20/0.52  fof(f244,plain,(
% 0.20/0.52    spl3_23 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.52  fof(f242,plain,(
% 0.20/0.52    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_3 | ~spl3_4 | ~spl3_20)),
% 0.20/0.52    inference(subsumption_resolution,[],[f241,f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ~v2_struct_0(sK1) | spl3_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    spl3_3 <=> v2_struct_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.52  fof(f241,plain,(
% 0.20/0.52    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_20)),
% 0.20/0.52    inference(subsumption_resolution,[],[f240,f102])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    l1_struct_0(sK1) | ~spl3_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f100])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    spl3_4 <=> l1_struct_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.52  fof(f240,plain,(
% 0.20/0.52    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_20),
% 0.20/0.52    inference(superposition,[],[f61,f216])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.20/0.52  fof(f374,plain,(
% 0.20/0.52    u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | v1_xboole_0(k2_relat_1(sK2)) | ~v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f338,plain,(
% 0.20/0.52    spl3_35 | ~spl3_14 | ~spl3_21 | ~spl3_31),
% 0.20/0.52    inference(avatar_split_clause,[],[f330,f308,f218,f184,f335])).
% 0.20/0.52  fof(f184,plain,(
% 0.20/0.52    spl3_14 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.52  fof(f218,plain,(
% 0.20/0.52    spl3_21 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.52  fof(f330,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k2_struct_0(sK0) | (~spl3_14 | ~spl3_21 | ~spl3_31)),
% 0.20/0.52    inference(subsumption_resolution,[],[f230,f309])).
% 0.20/0.52  fof(f230,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k2_struct_0(sK0) | ~v1_relat_1(sK2) | (~spl3_14 | ~spl3_21)),
% 0.20/0.52    inference(subsumption_resolution,[],[f229,f186])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f184])).
% 0.20/0.52  fof(f229,plain,(
% 0.20/0.52    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k1_relat_1(sK2) = k2_struct_0(sK0) | ~v1_relat_1(sK2) | ~spl3_21),
% 0.20/0.52    inference(resolution,[],[f220,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.52  fof(f220,plain,(
% 0.20/0.52    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_21),
% 0.20/0.52    inference(avatar_component_clause,[],[f218])).
% 0.20/0.52  fof(f329,plain,(
% 0.20/0.52    ~spl3_13 | spl3_31),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f328])).
% 0.20/0.52  fof(f328,plain,(
% 0.20/0.52    $false | (~spl3_13 | spl3_31)),
% 0.20/0.52    inference(subsumption_resolution,[],[f327,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.52  fof(f327,plain,(
% 0.20/0.52    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_13 | spl3_31)),
% 0.20/0.52    inference(resolution,[],[f315,f159])).
% 0.20/0.52  fof(f315,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_31),
% 0.20/0.52    inference(resolution,[],[f310,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.52  fof(f310,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | spl3_31),
% 0.20/0.52    inference(avatar_component_clause,[],[f308])).
% 0.20/0.52  fof(f326,plain,(
% 0.20/0.52    spl3_33 | spl3_34 | ~spl3_1 | ~spl3_12 | ~spl3_13 | ~spl3_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f318,f214,f157,f151,f85,f323,f320])).
% 0.20/0.52  fof(f323,plain,(
% 0.20/0.52    spl3_34 <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    spl3_12 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.52  fof(f318,plain,(
% 0.20/0.52    ( ! [X0] : (r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0)) ) | (~spl3_1 | ~spl3_12 | ~spl3_13 | ~spl3_20)),
% 0.20/0.52    inference(forward_demodulation,[],[f317,f216])).
% 0.20/0.52  fof(f317,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_12 | ~spl3_13 | ~spl3_20)),
% 0.20/0.52    inference(forward_demodulation,[],[f316,f216])).
% 0.20/0.52  fof(f316,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_12 | ~spl3_13 | ~spl3_20)),
% 0.20/0.52    inference(forward_demodulation,[],[f181,f216])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f180,f87])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f168,f153])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f151])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | ~spl3_13),
% 0.20/0.52    inference(resolution,[],[f159,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.20/0.52  fof(f301,plain,(
% 0.20/0.52    spl3_29 | ~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f296,f214,f210,f157,f151,f90,f85,f298])).
% 0.20/0.52  fof(f298,plain,(
% 0.20/0.52    spl3_29 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.52  fof(f210,plain,(
% 0.20/0.52    spl3_19 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.52  fof(f296,plain,(
% 0.20/0.52    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_20)),
% 0.20/0.52    inference(forward_demodulation,[],[f295,f216])).
% 0.20/0.52  fof(f295,plain,(
% 0.20/0.52    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_20)),
% 0.20/0.52    inference(subsumption_resolution,[],[f294,f212])).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f210])).
% 0.20/0.52  fof(f294,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_20)),
% 0.20/0.52    inference(forward_demodulation,[],[f179,f216])).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f178,f92])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f177,f87])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f167,f153])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.20/0.52    inference(resolution,[],[f159,f81])).
% 0.20/0.52  fof(f275,plain,(
% 0.20/0.52    spl3_27 | ~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f265,f214,f210,f157,f151,f90,f85,f272])).
% 0.20/0.52  fof(f265,plain,(
% 0.20/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_20)),
% 0.20/0.52    inference(forward_demodulation,[],[f264,f216])).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_20)),
% 0.20/0.52    inference(subsumption_resolution,[],[f263,f212])).
% 0.20/0.52  fof(f263,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_20)),
% 0.20/0.52    inference(forward_demodulation,[],[f176,f216])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f175,f92])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f174,f87])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f166,f153])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl3_13),
% 0.20/0.52    inference(resolution,[],[f159,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.52  fof(f270,plain,(
% 0.20/0.52    spl3_26 | ~spl3_12 | ~spl3_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f239,f214,f151,f267])).
% 0.20/0.52  fof(f239,plain,(
% 0.20/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_12 | ~spl3_20)),
% 0.20/0.52    inference(superposition,[],[f153,f216])).
% 0.20/0.52  fof(f262,plain,(
% 0.20/0.52    spl3_25 | ~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f257,f214,f210,f157,f151,f90,f85,f259])).
% 0.20/0.52  fof(f257,plain,(
% 0.20/0.52    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_20)),
% 0.20/0.52    inference(forward_demodulation,[],[f256,f216])).
% 0.20/0.52  fof(f256,plain,(
% 0.20/0.52    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_20)),
% 0.20/0.52    inference(subsumption_resolution,[],[f255,f212])).
% 0.20/0.52  fof(f255,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_20)),
% 0.20/0.52    inference(forward_demodulation,[],[f173,f216])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f172,f92])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f171,f87])).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f165,f153])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~spl3_13),
% 0.20/0.52    inference(resolution,[],[f159,f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    spl3_21 | spl3_22 | ~spl3_1 | ~spl3_12 | ~spl3_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f170,f157,f151,f85,f222,f218])).
% 0.20/0.52  fof(f222,plain,(
% 0.20/0.52    spl3_22 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    v1_xboole_0(k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f169,f153])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_13)),
% 0.20/0.52    inference(subsumption_resolution,[],[f161,f87])).
% 0.20/0.52  fof(f161,plain,(
% 0.20/0.52    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.20/0.52    inference(resolution,[],[f159,f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.52    inference(flattening,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    spl3_17 | ~spl3_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f162,f157,f201])).
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    spl3_17 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.20/0.52    inference(resolution,[],[f159,f75])).
% 0.20/0.52  fof(f199,plain,(
% 0.20/0.52    ~spl3_16 | ~spl3_7 | ~spl3_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f189,f129,f119,f196])).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    spl3_16 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    spl3_7 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_7 | ~spl3_9)),
% 0.20/0.52    inference(forward_demodulation,[],[f188,f131])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f129])).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~spl3_7),
% 0.20/0.52    inference(forward_demodulation,[],[f53,f121])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f119])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f18])).
% 0.20/0.52  fof(f18,conjecture,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    spl3_14 | ~spl3_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f163,f157,f184])).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.20/0.52    inference(resolution,[],[f159,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    spl3_13 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f147,f129,f124,f119,f157])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.20/0.52    inference(forward_demodulation,[],[f143,f131])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8)),
% 0.20/0.52    inference(forward_demodulation,[],[f126,f121])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f124])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    spl3_12 | ~spl3_6 | ~spl3_7 | ~spl3_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f146,f129,f119,f114,f151])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_7 | ~spl3_9)),
% 0.20/0.52    inference(forward_demodulation,[],[f145,f121])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl3_6 | ~spl3_9)),
% 0.20/0.52    inference(superposition,[],[f116,f131])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f114])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    spl3_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f51,f134])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    spl3_10 <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    spl3_9 | ~spl3_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f112,f105,f129])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    spl3_5 <=> l1_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.20/0.52    inference(resolution,[],[f107,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    l1_struct_0(sK0) | ~spl3_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f105])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    spl3_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f50,f124])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    spl3_7 | ~spl3_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f111,f100,f119])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_4),
% 0.20/0.52    inference(resolution,[],[f102,f59])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    spl3_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f49,f114])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    spl3_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f56,f105])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    l1_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    spl3_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f55,f100])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    l1_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ~spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f54,f95])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ~v2_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f52,f90])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    v2_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl3_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f48,f85])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    v1_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (3573)------------------------------
% 0.20/0.52  % (3573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3573)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (3573)Memory used [KB]: 11129
% 0.20/0.52  % (3573)Time elapsed: 0.104 s
% 0.20/0.52  % (3573)------------------------------
% 0.20/0.52  % (3573)------------------------------
% 0.20/0.52  % (3569)Success in time 0.171 s
%------------------------------------------------------------------------------
