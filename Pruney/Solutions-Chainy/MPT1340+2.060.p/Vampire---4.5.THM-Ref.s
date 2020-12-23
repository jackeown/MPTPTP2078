%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:26 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  296 ( 581 expanded)
%              Number of leaves         :   61 ( 238 expanded)
%              Depth                    :   16
%              Number of atoms          : 1251 (2107 expanded)
%              Number of equality atoms :  184 ( 323 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f771,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f117,f122,f127,f132,f137,f157,f164,f198,f203,f214,f233,f234,f267,f268,f290,f300,f303,f341,f354,f360,f427,f434,f463,f484,f511,f522,f574,f580,f611,f619,f676,f756,f757,f770])).

fof(f770,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_28
    | spl3_61 ),
    inference(avatar_contradiction_clause,[],[f769])).

fof(f769,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_28
    | spl3_61 ),
    inference(subsumption_resolution,[],[f768,f273])).

fof(f273,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl3_28
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f768,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_61 ),
    inference(subsumption_resolution,[],[f767,f92])).

fof(f92,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f767,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_61 ),
    inference(subsumption_resolution,[],[f766,f87])).

fof(f87,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f766,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_61 ),
    inference(trivial_inequality_removal,[],[f765])).

fof(f765,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_61 ),
    inference(superposition,[],[f567,f64])).

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

fof(f567,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | spl3_61 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl3_61
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f757,plain,
    ( sK2 != k2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_struct_0(sK0)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f756,plain,
    ( spl3_76
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52
    | ~ spl3_60
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f749,f566,f562,f494,f490,f417,f272,f90,f85,f753])).

fof(f753,plain,
    ( spl3_76
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f417,plain,
    ( spl3_44
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f490,plain,
    ( spl3_51
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f494,plain,
    ( spl3_52
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f562,plain,
    ( spl3_60
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f749,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52
    | ~ spl3_60
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f748,f92])).

fof(f748,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52
    | ~ spl3_60
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f747,f87])).

fof(f747,plain,
    ( ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52
    | ~ spl3_60
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f746,f273])).

fof(f746,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52
    | ~ spl3_60
    | ~ spl3_61 ),
    inference(trivial_inequality_removal,[],[f745])).

fof(f745,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52
    | ~ spl3_60
    | ~ spl3_61 ),
    inference(duplicate_literal_removal,[],[f743])).

fof(f743,plain,
    ( k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52
    | ~ spl3_60
    | ~ spl3_61 ),
    inference(superposition,[],[f643,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
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

fof(f643,plain,
    ( ! [X0] :
        ( k5_relat_1(k2_funct_1(sK2),X0) != k6_relat_1(k2_relat_1(sK2))
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_funct_1(k2_funct_1(sK2)) = X0 )
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52
    | ~ spl3_60
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f642,f568])).

fof(f568,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f566])).

fof(f642,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k5_relat_1(k2_funct_1(sK2),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
        | k2_funct_1(k2_funct_1(sK2)) = X0 )
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52
    | ~ spl3_60 ),
    inference(forward_demodulation,[],[f641,f495])).

fof(f495,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f494])).

fof(f641,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2))
        | k5_relat_1(k2_funct_1(sK2),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
        | k2_funct_1(k2_funct_1(sK2)) = X0 )
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_60 ),
    inference(subsumption_resolution,[],[f640,f563])).

fof(f563,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f562])).

fof(f640,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2))
        | k5_relat_1(k2_funct_1(sK2),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
        | k2_funct_1(k2_funct_1(sK2)) = X0 )
    | ~ spl3_44
    | ~ spl3_51 ),
    inference(subsumption_resolution,[],[f639,f418])).

fof(f418,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f417])).

fof(f639,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2))
        | k5_relat_1(k2_funct_1(sK2),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
        | k2_funct_1(k2_funct_1(sK2)) = X0 )
    | ~ spl3_51 ),
    inference(resolution,[],[f491,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
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
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
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
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f491,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f490])).

fof(f676,plain,
    ( spl3_65
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_37
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f666,f513,f490,f417,f357,f297,f287,f673])).

fof(f673,plain,
    ( spl3_65
  <=> k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f287,plain,
    ( spl3_30
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f297,plain,
    ( spl3_31
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f357,plain,
    ( spl3_37
  <=> k1_relat_1(sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f513,plain,
    ( spl3_54
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f666,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_37
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f632,f491])).

fof(f632,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_37
    | ~ spl3_44
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f631,f359])).

fof(f359,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f357])).

fof(f631,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_37
    | ~ spl3_44
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f630,f515])).

fof(f515,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f513])).

fof(f630,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_37
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f629,f359])).

fof(f629,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f317,f418])).

fof(f317,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f311,f289])).

fof(f289,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f287])).

fof(f311,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_31 ),
    inference(resolution,[],[f299,f81])).

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

fof(f299,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f297])).

fof(f619,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_28
    | spl3_62 ),
    inference(avatar_contradiction_clause,[],[f618])).

fof(f618,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_28
    | spl3_62 ),
    inference(subsumption_resolution,[],[f617,f273])).

fof(f617,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_62 ),
    inference(subsumption_resolution,[],[f616,f92])).

fof(f616,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_62 ),
    inference(subsumption_resolution,[],[f615,f87])).

fof(f615,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_62 ),
    inference(subsumption_resolution,[],[f614,f58])).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f614,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_62 ),
    inference(superposition,[],[f610,f67])).

fof(f610,plain,
    ( ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | spl3_62 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl3_62
  <=> v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f611,plain,
    ( ~ spl3_62
    | ~ spl3_1
    | ~ spl3_28
    | ~ spl3_44
    | spl3_51
    | ~ spl3_52
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f595,f562,f494,f490,f417,f272,f85,f608])).

fof(f595,plain,
    ( ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ spl3_1
    | ~ spl3_28
    | ~ spl3_44
    | spl3_51
    | ~ spl3_52
    | ~ spl3_60 ),
    inference(subsumption_resolution,[],[f594,f273])).

fof(f594,plain,
    ( ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_44
    | spl3_51
    | ~ spl3_52
    | ~ spl3_60 ),
    inference(subsumption_resolution,[],[f589,f87])).

fof(f589,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_44
    | spl3_51
    | ~ spl3_52
    | ~ spl3_60 ),
    inference(equality_resolution,[],[f586])).

fof(f586,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_44
    | spl3_51
    | ~ spl3_52
    | ~ spl3_60 ),
    inference(forward_demodulation,[],[f585,f495])).

fof(f585,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0))
        | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl3_44
    | spl3_51
    | ~ spl3_60 ),
    inference(subsumption_resolution,[],[f504,f563])).

fof(f504,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0))
        | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl3_44
    | spl3_51 ),
    inference(subsumption_resolution,[],[f502,f418])).

fof(f502,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0))
        | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X0) )
    | spl3_51 ),
    inference(resolution,[],[f492,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
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

fof(f492,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_51 ),
    inference(avatar_component_clause,[],[f490])).

fof(f580,plain,
    ( ~ spl3_1
    | ~ spl3_35
    | ~ spl3_37
    | ~ spl3_45
    | ~ spl3_50 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_35
    | ~ spl3_37
    | ~ spl3_45
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f578,f433])).

fof(f433,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl3_45
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f578,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_35
    | ~ spl3_37
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f577,f87])).

fof(f577,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_35
    | ~ spl3_37
    | ~ spl3_50 ),
    inference(resolution,[],[f384,f483])).

fof(f483,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f481])).

fof(f481,plain,
    ( spl3_50
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f384,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) )
    | ~ spl3_35
    | ~ spl3_37 ),
    inference(superposition,[],[f349,f359])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl3_35
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f574,plain,
    ( ~ spl3_1
    | ~ spl3_28
    | spl3_60 ),
    inference(avatar_contradiction_clause,[],[f573])).

fof(f573,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_28
    | spl3_60 ),
    inference(subsumption_resolution,[],[f572,f273])).

fof(f572,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_60 ),
    inference(subsumption_resolution,[],[f570,f87])).

fof(f570,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_60 ),
    inference(resolution,[],[f564,f62])).

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

fof(f564,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_60 ),
    inference(avatar_component_clause,[],[f562])).

fof(f522,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f511,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_28
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_28
    | spl3_52 ),
    inference(subsumption_resolution,[],[f509,f273])).

fof(f509,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_52 ),
    inference(subsumption_resolution,[],[f508,f92])).

fof(f508,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_52 ),
    inference(subsumption_resolution,[],[f507,f87])).

fof(f507,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_52 ),
    inference(trivial_inequality_removal,[],[f506])).

fof(f506,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_52 ),
    inference(superposition,[],[f496,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f496,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f494])).

fof(f484,plain,
    ( spl3_50
    | ~ spl3_27
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f379,f357,f264,f481])).

fof(f264,plain,
    ( spl3_27
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f379,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_27
    | ~ spl3_37 ),
    inference(superposition,[],[f265,f359])).

fof(f265,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f264])).

fof(f463,plain,
    ( spl3_47
    | ~ spl3_31
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f457,f357,f297,f460])).

fof(f460,plain,
    ( spl3_47
  <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f457,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_31
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f306,f359])).

fof(f306,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_31 ),
    inference(resolution,[],[f299,f75])).

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

fof(f434,plain,
    ( spl3_45
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f404,f357,f224,f161,f431])).

fof(f161,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f224,plain,
    ( spl3_22
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f404,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f244,f359])).

fof(f244,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(superposition,[],[f163,f226])).

fof(f226,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f224])).

fof(f163,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f427,plain,
    ( ~ spl3_1
    | ~ spl3_28
    | spl3_44 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_28
    | spl3_44 ),
    inference(subsumption_resolution,[],[f425,f273])).

fof(f425,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_44 ),
    inference(subsumption_resolution,[],[f422,f87])).

fof(f422,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_44 ),
    inference(resolution,[],[f419,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f419,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f417])).

fof(f360,plain,
    ( spl3_37
    | ~ spl3_17
    | ~ spl3_26
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f355,f272,f260,f200,f357])).

fof(f200,plain,
    ( spl3_17
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f260,plain,
    ( spl3_26
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f355,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ spl3_17
    | ~ spl3_26
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f270,f273])).

fof(f270,plain,
    ( k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f269,f202])).

fof(f202,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f269,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k1_relat_1(sK2) = k2_struct_0(sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_26 ),
    inference(resolution,[],[f262,f74])).

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

fof(f262,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f260])).

fof(f354,plain,
    ( spl3_35
    | spl3_36
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f346,f264,f224,f161,f85,f351,f348])).

fof(f351,plain,
    ( spl3_36
  <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f346,plain,
    ( ! [X0] :
        ( r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f345,f226])).

fof(f345,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f344,f226])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f343,f226])).

fof(f343,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f342,f265])).

fof(f342,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f190,f226])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f181,f87])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
        | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) )
    | ~ spl3_13 ),
    inference(resolution,[],[f163,f82])).

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

fof(f341,plain,
    ( spl3_34
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f331,f264,f224,f220,f161,f90,f85,f338])).

fof(f338,plain,
    ( spl3_34
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f220,plain,
    ( spl3_21
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f331,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f330,f226])).

fof(f330,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f329,f222])).

fof(f222,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f220])).

fof(f329,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f328,f226])).

fof(f328,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f327,f265])).

fof(f327,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f189,f226])).

fof(f189,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f188,f92])).

fof(f188,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f180,f87])).

fof(f180,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f163,f81])).

fof(f303,plain,
    ( ~ spl3_13
    | spl3_28 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl3_13
    | spl3_28 ),
    inference(subsumption_resolution,[],[f301,f71])).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f301,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_13
    | spl3_28 ),
    inference(resolution,[],[f279,f163])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_28 ),
    inference(resolution,[],[f274,f60])).

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

fof(f274,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f272])).

fof(f300,plain,
    ( spl3_31
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f295,f264,f224,f220,f161,f90,f85,f297])).

fof(f295,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f294,f226])).

fof(f294,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f293,f222])).

fof(f293,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f292,f226])).

fof(f292,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f291,f265])).

fof(f291,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f187,f226])).

fof(f187,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f186,f92])).

fof(f186,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f179,f87])).

fof(f179,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_13 ),
    inference(resolution,[],[f163,f80])).

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

fof(f290,plain,
    ( spl3_30
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f284,f264,f224,f220,f161,f90,f85,f287])).

fof(f284,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f283,f226])).

fof(f283,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f282,f222])).

fof(f282,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f281,f226])).

% (9037)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f281,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_22
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f280,f265])).

fof(f280,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f185,f226])).

fof(f185,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f184,f92])).

fof(f184,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f178,f87])).

fof(f178,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f163,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f268,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f267,plain,
    ( spl3_26
    | ~ spl3_27
    | ~ spl3_1
    | spl3_12
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f258,f224,f161,f154,f85,f264,f260])).

fof(f154,plain,
    ( spl3_12
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f258,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | spl3_12
    | ~ spl3_13
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f183,f226])).

fof(f183,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f182,f87])).

fof(f182,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_12
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f174,f156])).

fof(f156,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f174,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f163,f72])).

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

fof(f234,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f233,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f214,plain,
    ( spl3_19
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f175,f161,f211])).

fof(f211,plain,
    ( spl3_19
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f175,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f163,f75])).

fof(f203,plain,
    ( spl3_17
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f176,f161,f200])).

fof(f176,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f163,f76])).

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

fof(f198,plain,
    ( ~ spl3_16
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f193,f129,f119,f195])).

% (9024)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f195,plain,
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

% (9041)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f193,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f192,f131])).

fof(f131,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f192,plain,
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

fof(f164,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f152,f129,f124,f119,f161])).

fof(f124,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f152,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f146,f131])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f126,f121])).

fof(f126,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f157,plain,
    ( ~ spl3_12
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f145,f119,f100,f95,f154])).

fof(f95,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f100,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f145,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f144,f97])).

fof(f97,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f144,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f143,f102])).

fof(f102,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f143,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f61,f121])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

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

fof(f114,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:57:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (9026)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (9034)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (9033)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (9023)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (9031)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (9042)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (9032)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (9027)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (9043)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (9035)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (9029)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (9030)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (9043)Refutation not found, incomplete strategy% (9043)------------------------------
% 0.22/0.51  % (9043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9043)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9043)Memory used [KB]: 10618
% 0.22/0.51  % (9043)Time elapsed: 0.092 s
% 0.22/0.51  % (9043)------------------------------
% 0.22/0.51  % (9043)------------------------------
% 1.21/0.52  % (9028)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.21/0.52  % (9023)Refutation not found, incomplete strategy% (9023)------------------------------
% 1.21/0.52  % (9023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (9023)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (9023)Memory used [KB]: 6524
% 1.21/0.52  % (9023)Time elapsed: 0.093 s
% 1.21/0.52  % (9023)------------------------------
% 1.21/0.52  % (9023)------------------------------
% 1.21/0.52  % (9038)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.21/0.52  % (9025)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.21/0.52  % (9040)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.21/0.52  % (9026)Refutation found. Thanks to Tanya!
% 1.21/0.52  % SZS status Theorem for theBenchmark
% 1.21/0.52  % SZS output start Proof for theBenchmark
% 1.21/0.52  fof(f771,plain,(
% 1.21/0.52    $false),
% 1.21/0.52    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f117,f122,f127,f132,f137,f157,f164,f198,f203,f214,f233,f234,f267,f268,f290,f300,f303,f341,f354,f360,f427,f434,f463,f484,f511,f522,f574,f580,f611,f619,f676,f756,f757,f770])).
% 1.21/0.52  fof(f770,plain,(
% 1.21/0.52    ~spl3_1 | ~spl3_2 | ~spl3_28 | spl3_61),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f769])).
% 1.21/0.52  fof(f769,plain,(
% 1.21/0.52    $false | (~spl3_1 | ~spl3_2 | ~spl3_28 | spl3_61)),
% 1.21/0.52    inference(subsumption_resolution,[],[f768,f273])).
% 1.21/0.52  fof(f273,plain,(
% 1.21/0.52    v1_relat_1(sK2) | ~spl3_28),
% 1.21/0.52    inference(avatar_component_clause,[],[f272])).
% 1.21/0.52  fof(f272,plain,(
% 1.21/0.52    spl3_28 <=> v1_relat_1(sK2)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.21/0.52  fof(f768,plain,(
% 1.21/0.52    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | spl3_61)),
% 1.21/0.52    inference(subsumption_resolution,[],[f767,f92])).
% 1.21/0.52  fof(f92,plain,(
% 1.21/0.52    v2_funct_1(sK2) | ~spl3_2),
% 1.21/0.52    inference(avatar_component_clause,[],[f90])).
% 1.21/0.52  fof(f90,plain,(
% 1.21/0.52    spl3_2 <=> v2_funct_1(sK2)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.21/0.52  fof(f767,plain,(
% 1.21/0.52    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_61)),
% 1.21/0.52    inference(subsumption_resolution,[],[f766,f87])).
% 1.21/0.52  fof(f87,plain,(
% 1.21/0.52    v1_funct_1(sK2) | ~spl3_1),
% 1.21/0.52    inference(avatar_component_clause,[],[f85])).
% 1.21/0.52  fof(f85,plain,(
% 1.21/0.52    spl3_1 <=> v1_funct_1(sK2)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.21/0.52  fof(f766,plain,(
% 1.21/0.52    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_61),
% 1.21/0.52    inference(trivial_inequality_removal,[],[f765])).
% 1.21/0.52  fof(f765,plain,(
% 1.21/0.52    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_61),
% 1.21/0.52    inference(superposition,[],[f567,f64])).
% 1.21/0.52  fof(f64,plain,(
% 1.21/0.52    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f29])).
% 1.21/0.52  fof(f29,plain,(
% 1.21/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.52    inference(flattening,[],[f28])).
% 1.21/0.52  fof(f28,plain,(
% 1.21/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f6])).
% 1.21/0.52  fof(f6,axiom,(
% 1.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.21/0.52  fof(f567,plain,(
% 1.21/0.52    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | spl3_61),
% 1.21/0.52    inference(avatar_component_clause,[],[f566])).
% 1.21/0.52  fof(f566,plain,(
% 1.21/0.52    spl3_61 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 1.21/0.52  fof(f757,plain,(
% 1.21/0.52    sK2 != k2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_struct_0(sK0) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 1.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 1.21/0.52  fof(f756,plain,(
% 1.21/0.52    spl3_76 | ~spl3_1 | ~spl3_2 | ~spl3_28 | ~spl3_44 | ~spl3_51 | ~spl3_52 | ~spl3_60 | ~spl3_61),
% 1.21/0.52    inference(avatar_split_clause,[],[f749,f566,f562,f494,f490,f417,f272,f90,f85,f753])).
% 1.21/0.52  fof(f753,plain,(
% 1.21/0.52    spl3_76 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 1.21/0.52  fof(f417,plain,(
% 1.21/0.52    spl3_44 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.21/0.52  fof(f490,plain,(
% 1.21/0.52    spl3_51 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 1.21/0.52  fof(f494,plain,(
% 1.21/0.52    spl3_52 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 1.21/0.52  fof(f562,plain,(
% 1.21/0.52    spl3_60 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 1.21/0.52  fof(f749,plain,(
% 1.21/0.52    sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_28 | ~spl3_44 | ~spl3_51 | ~spl3_52 | ~spl3_60 | ~spl3_61)),
% 1.21/0.52    inference(subsumption_resolution,[],[f748,f92])).
% 1.21/0.52  fof(f748,plain,(
% 1.21/0.52    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | (~spl3_1 | ~spl3_28 | ~spl3_44 | ~spl3_51 | ~spl3_52 | ~spl3_60 | ~spl3_61)),
% 1.21/0.52    inference(subsumption_resolution,[],[f747,f87])).
% 1.21/0.52  fof(f747,plain,(
% 1.21/0.52    ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | (~spl3_28 | ~spl3_44 | ~spl3_51 | ~spl3_52 | ~spl3_60 | ~spl3_61)),
% 1.21/0.52    inference(subsumption_resolution,[],[f746,f273])).
% 1.21/0.52  fof(f746,plain,(
% 1.21/0.52    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | (~spl3_44 | ~spl3_51 | ~spl3_52 | ~spl3_60 | ~spl3_61)),
% 1.21/0.52    inference(trivial_inequality_removal,[],[f745])).
% 1.21/0.52  fof(f745,plain,(
% 1.21/0.52    k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | (~spl3_44 | ~spl3_51 | ~spl3_52 | ~spl3_60 | ~spl3_61)),
% 1.21/0.52    inference(duplicate_literal_removal,[],[f743])).
% 1.21/0.52  fof(f743,plain,(
% 1.21/0.52    k6_relat_1(k2_relat_1(sK2)) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_44 | ~spl3_51 | ~spl3_52 | ~spl3_60 | ~spl3_61)),
% 1.21/0.52    inference(superposition,[],[f643,f67])).
% 1.21/0.52  fof(f67,plain,(
% 1.21/0.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f31])).
% 1.21/0.52  fof(f31,plain,(
% 1.21/0.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.52    inference(flattening,[],[f30])).
% 1.21/0.52  fof(f30,plain,(
% 1.21/0.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f7])).
% 1.21/0.52  fof(f7,axiom,(
% 1.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.21/0.52  fof(f643,plain,(
% 1.21/0.52    ( ! [X0] : (k5_relat_1(k2_funct_1(sK2),X0) != k6_relat_1(k2_relat_1(sK2)) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_funct_1(k2_funct_1(sK2)) = X0) ) | (~spl3_44 | ~spl3_51 | ~spl3_52 | ~spl3_60 | ~spl3_61)),
% 1.21/0.52    inference(forward_demodulation,[],[f642,f568])).
% 1.21/0.52  fof(f568,plain,(
% 1.21/0.52    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_61),
% 1.21/0.52    inference(avatar_component_clause,[],[f566])).
% 1.21/0.52  fof(f642,plain,(
% 1.21/0.52    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k5_relat_1(k2_funct_1(sK2),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k2_funct_1(k2_funct_1(sK2)) = X0) ) | (~spl3_44 | ~spl3_51 | ~spl3_52 | ~spl3_60)),
% 1.21/0.52    inference(forward_demodulation,[],[f641,f495])).
% 1.21/0.52  fof(f495,plain,(
% 1.21/0.52    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_52),
% 1.21/0.52    inference(avatar_component_clause,[],[f494])).
% 1.21/0.52  fof(f641,plain,(
% 1.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2)) | k5_relat_1(k2_funct_1(sK2),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k2_funct_1(k2_funct_1(sK2)) = X0) ) | (~spl3_44 | ~spl3_51 | ~spl3_60)),
% 1.21/0.52    inference(subsumption_resolution,[],[f640,f563])).
% 1.21/0.52  fof(f563,plain,(
% 1.21/0.52    v1_relat_1(k2_funct_1(sK2)) | ~spl3_60),
% 1.21/0.52    inference(avatar_component_clause,[],[f562])).
% 1.21/0.52  fof(f640,plain,(
% 1.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2)) | k5_relat_1(k2_funct_1(sK2),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k2_funct_1(k2_funct_1(sK2)) = X0) ) | (~spl3_44 | ~spl3_51)),
% 1.21/0.52    inference(subsumption_resolution,[],[f639,f418])).
% 1.21/0.52  fof(f418,plain,(
% 1.21/0.52    v1_funct_1(k2_funct_1(sK2)) | ~spl3_44),
% 1.21/0.52    inference(avatar_component_clause,[],[f417])).
% 1.21/0.52  fof(f639,plain,(
% 1.21/0.52    ( ! [X0] : (~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2)) | k5_relat_1(k2_funct_1(sK2),X0) != k6_relat_1(k1_relat_1(k2_funct_1(sK2))) | k2_funct_1(k2_funct_1(sK2)) = X0) ) | ~spl3_51),
% 1.21/0.52    inference(resolution,[],[f491,f68])).
% 1.21/0.52  fof(f68,plain,(
% 1.21/0.52    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_funct_1(X0) = X1) )),
% 1.21/0.52    inference(cnf_transformation,[],[f33])).
% 1.21/0.52  fof(f33,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.52    inference(flattening,[],[f32])).
% 1.21/0.52  fof(f32,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f8])).
% 1.21/0.52  fof(f8,axiom,(
% 1.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 1.21/0.52  fof(f491,plain,(
% 1.21/0.52    v2_funct_1(k2_funct_1(sK2)) | ~spl3_51),
% 1.21/0.52    inference(avatar_component_clause,[],[f490])).
% 1.21/0.52  fof(f676,plain,(
% 1.21/0.52    spl3_65 | ~spl3_30 | ~spl3_31 | ~spl3_37 | ~spl3_44 | ~spl3_51 | ~spl3_54),
% 1.21/0.52    inference(avatar_split_clause,[],[f666,f513,f490,f417,f357,f297,f287,f673])).
% 1.21/0.52  fof(f673,plain,(
% 1.21/0.52    spl3_65 <=> k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 1.21/0.52  fof(f287,plain,(
% 1.21/0.52    spl3_30 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.21/0.52  fof(f297,plain,(
% 1.21/0.52    spl3_31 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.21/0.52  fof(f357,plain,(
% 1.21/0.52    spl3_37 <=> k1_relat_1(sK2) = k2_struct_0(sK0)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.21/0.52  fof(f513,plain,(
% 1.21/0.52    spl3_54 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 1.21/0.52  fof(f666,plain,(
% 1.21/0.52    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_30 | ~spl3_31 | ~spl3_37 | ~spl3_44 | ~spl3_51 | ~spl3_54)),
% 1.21/0.52    inference(subsumption_resolution,[],[f632,f491])).
% 1.21/0.52  fof(f632,plain,(
% 1.21/0.52    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_30 | ~spl3_31 | ~spl3_37 | ~spl3_44 | ~spl3_54)),
% 1.21/0.52    inference(forward_demodulation,[],[f631,f359])).
% 1.21/0.52  fof(f359,plain,(
% 1.21/0.52    k1_relat_1(sK2) = k2_struct_0(sK0) | ~spl3_37),
% 1.21/0.52    inference(avatar_component_clause,[],[f357])).
% 1.21/0.52  fof(f631,plain,(
% 1.21/0.52    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_30 | ~spl3_31 | ~spl3_37 | ~spl3_44 | ~spl3_54)),
% 1.21/0.52    inference(subsumption_resolution,[],[f630,f515])).
% 1.21/0.52  fof(f515,plain,(
% 1.21/0.52    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_54),
% 1.21/0.52    inference(avatar_component_clause,[],[f513])).
% 1.21/0.52  fof(f630,plain,(
% 1.21/0.52    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_30 | ~spl3_31 | ~spl3_37 | ~spl3_44)),
% 1.21/0.52    inference(forward_demodulation,[],[f629,f359])).
% 1.21/0.52  fof(f629,plain,(
% 1.21/0.52    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_30 | ~spl3_31 | ~spl3_44)),
% 1.21/0.52    inference(subsumption_resolution,[],[f317,f418])).
% 1.21/0.52  fof(f317,plain,(
% 1.21/0.52    ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_30 | ~spl3_31)),
% 1.21/0.52    inference(subsumption_resolution,[],[f311,f289])).
% 1.21/0.52  fof(f289,plain,(
% 1.21/0.52    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_30),
% 1.21/0.52    inference(avatar_component_clause,[],[f287])).
% 1.21/0.52  fof(f311,plain,(
% 1.21/0.52    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_31),
% 1.21/0.52    inference(resolution,[],[f299,f81])).
% 1.21/0.52  fof(f81,plain,(
% 1.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f45])).
% 1.21/0.52  fof(f45,plain,(
% 1.21/0.52    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.21/0.52    inference(flattening,[],[f44])).
% 1.21/0.52  fof(f44,plain,(
% 1.21/0.52    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.21/0.52    inference(ennf_transformation,[],[f17])).
% 1.21/0.52  fof(f17,axiom,(
% 1.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 1.21/0.52  fof(f299,plain,(
% 1.21/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_31),
% 1.21/0.52    inference(avatar_component_clause,[],[f297])).
% 1.21/0.52  fof(f619,plain,(
% 1.21/0.52    ~spl3_1 | ~spl3_2 | ~spl3_28 | spl3_62),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f618])).
% 1.21/0.52  fof(f618,plain,(
% 1.21/0.52    $false | (~spl3_1 | ~spl3_2 | ~spl3_28 | spl3_62)),
% 1.21/0.52    inference(subsumption_resolution,[],[f617,f273])).
% 1.21/0.52  fof(f617,plain,(
% 1.21/0.52    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | spl3_62)),
% 1.21/0.52    inference(subsumption_resolution,[],[f616,f92])).
% 1.21/0.52  fof(f616,plain,(
% 1.21/0.52    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_62)),
% 1.21/0.52    inference(subsumption_resolution,[],[f615,f87])).
% 1.21/0.52  fof(f615,plain,(
% 1.21/0.52    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_62),
% 1.21/0.52    inference(subsumption_resolution,[],[f614,f58])).
% 1.21/0.52  fof(f58,plain,(
% 1.21/0.52    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.21/0.52    inference(cnf_transformation,[],[f4])).
% 1.21/0.52  fof(f4,axiom,(
% 1.21/0.52    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.21/0.52  fof(f614,plain,(
% 1.21/0.52    ~v2_funct_1(k6_relat_1(k2_relat_1(sK2))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_62),
% 1.21/0.52    inference(superposition,[],[f610,f67])).
% 1.21/0.52  fof(f610,plain,(
% 1.21/0.52    ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) | spl3_62),
% 1.21/0.52    inference(avatar_component_clause,[],[f608])).
% 1.21/0.52  fof(f608,plain,(
% 1.21/0.52    spl3_62 <=> v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 1.21/0.52  fof(f611,plain,(
% 1.21/0.52    ~spl3_62 | ~spl3_1 | ~spl3_28 | ~spl3_44 | spl3_51 | ~spl3_52 | ~spl3_60),
% 1.21/0.52    inference(avatar_split_clause,[],[f595,f562,f494,f490,f417,f272,f85,f608])).
% 1.21/0.52  fof(f595,plain,(
% 1.21/0.52    ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) | (~spl3_1 | ~spl3_28 | ~spl3_44 | spl3_51 | ~spl3_52 | ~spl3_60)),
% 1.21/0.52    inference(subsumption_resolution,[],[f594,f273])).
% 1.21/0.52  fof(f594,plain,(
% 1.21/0.52    ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_44 | spl3_51 | ~spl3_52 | ~spl3_60)),
% 1.21/0.52    inference(subsumption_resolution,[],[f589,f87])).
% 1.21/0.52  fof(f589,plain,(
% 1.21/0.52    ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) | ~v1_relat_1(sK2) | (~spl3_44 | spl3_51 | ~spl3_52 | ~spl3_60)),
% 1.21/0.52    inference(equality_resolution,[],[f586])).
% 1.21/0.52  fof(f586,plain,(
% 1.21/0.52    ( ! [X0] : (k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) | ~v1_relat_1(X0)) ) | (~spl3_44 | spl3_51 | ~spl3_52 | ~spl3_60)),
% 1.21/0.52    inference(forward_demodulation,[],[f585,f495])).
% 1.21/0.52  fof(f585,plain,(
% 1.21/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X0)) ) | (~spl3_44 | spl3_51 | ~spl3_60)),
% 1.21/0.52    inference(subsumption_resolution,[],[f504,f563])).
% 1.21/0.52  fof(f504,plain,(
% 1.21/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X0)) ) | (~spl3_44 | spl3_51)),
% 1.21/0.52    inference(subsumption_resolution,[],[f502,f418])).
% 1.21/0.52  fof(f502,plain,(
% 1.21/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X0)) ) | spl3_51),
% 1.21/0.52    inference(resolution,[],[f492,f69])).
% 1.21/0.52  fof(f69,plain,(
% 1.21/0.52    ( ! [X0,X1] : (v2_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f35])).
% 1.21/0.52  fof(f35,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.52    inference(flattening,[],[f34])).
% 1.21/0.52  fof(f34,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f5])).
% 1.21/0.52  fof(f5,axiom,(
% 1.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.21/0.52  fof(f492,plain,(
% 1.21/0.52    ~v2_funct_1(k2_funct_1(sK2)) | spl3_51),
% 1.21/0.52    inference(avatar_component_clause,[],[f490])).
% 1.21/0.52  fof(f580,plain,(
% 1.21/0.52    ~spl3_1 | ~spl3_35 | ~spl3_37 | ~spl3_45 | ~spl3_50),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f579])).
% 1.21/0.52  fof(f579,plain,(
% 1.21/0.52    $false | (~spl3_1 | ~spl3_35 | ~spl3_37 | ~spl3_45 | ~spl3_50)),
% 1.21/0.52    inference(subsumption_resolution,[],[f578,f433])).
% 1.21/0.52  fof(f433,plain,(
% 1.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_45),
% 1.21/0.52    inference(avatar_component_clause,[],[f431])).
% 1.21/0.52  fof(f431,plain,(
% 1.21/0.52    spl3_45 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 1.21/0.52  fof(f578,plain,(
% 1.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_35 | ~spl3_37 | ~spl3_50)),
% 1.21/0.52    inference(subsumption_resolution,[],[f577,f87])).
% 1.21/0.52  fof(f577,plain,(
% 1.21/0.52    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_35 | ~spl3_37 | ~spl3_50)),
% 1.21/0.52    inference(resolution,[],[f384,f483])).
% 1.21/0.52  fof(f483,plain,(
% 1.21/0.52    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_50),
% 1.21/0.52    inference(avatar_component_clause,[],[f481])).
% 1.21/0.52  fof(f481,plain,(
% 1.21/0.52    spl3_50 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 1.21/0.52  fof(f384,plain,(
% 1.21/0.52    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))) ) | (~spl3_35 | ~spl3_37)),
% 1.21/0.52    inference(superposition,[],[f349,f359])).
% 1.21/0.52  fof(f349,plain,(
% 1.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2))) ) | ~spl3_35),
% 1.21/0.52    inference(avatar_component_clause,[],[f348])).
% 1.21/0.52  fof(f348,plain,(
% 1.21/0.52    spl3_35 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)))),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 1.21/0.52  fof(f574,plain,(
% 1.21/0.52    ~spl3_1 | ~spl3_28 | spl3_60),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f573])).
% 1.21/0.52  fof(f573,plain,(
% 1.21/0.52    $false | (~spl3_1 | ~spl3_28 | spl3_60)),
% 1.21/0.52    inference(subsumption_resolution,[],[f572,f273])).
% 1.21/0.52  fof(f572,plain,(
% 1.21/0.52    ~v1_relat_1(sK2) | (~spl3_1 | spl3_60)),
% 1.21/0.52    inference(subsumption_resolution,[],[f570,f87])).
% 1.21/0.52  fof(f570,plain,(
% 1.21/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_60),
% 1.21/0.52    inference(resolution,[],[f564,f62])).
% 1.21/0.52  fof(f62,plain,(
% 1.21/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f27])).
% 1.21/0.52  fof(f27,plain,(
% 1.21/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.21/0.52    inference(flattening,[],[f26])).
% 1.21/0.52  fof(f26,plain,(
% 1.21/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f3])).
% 1.21/0.53  fof(f3,axiom,(
% 1.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.21/0.53  fof(f564,plain,(
% 1.21/0.53    ~v1_relat_1(k2_funct_1(sK2)) | spl3_60),
% 1.21/0.53    inference(avatar_component_clause,[],[f562])).
% 1.21/0.53  fof(f522,plain,(
% 1.21/0.53    k2_relat_1(k2_funct_1(sK2)) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.21/0.53  fof(f511,plain,(
% 1.21/0.53    ~spl3_1 | ~spl3_2 | ~spl3_28 | spl3_52),
% 1.21/0.53    inference(avatar_contradiction_clause,[],[f510])).
% 1.21/0.53  fof(f510,plain,(
% 1.21/0.53    $false | (~spl3_1 | ~spl3_2 | ~spl3_28 | spl3_52)),
% 1.21/0.53    inference(subsumption_resolution,[],[f509,f273])).
% 1.21/0.53  fof(f509,plain,(
% 1.21/0.53    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | spl3_52)),
% 1.21/0.53    inference(subsumption_resolution,[],[f508,f92])).
% 1.21/0.53  fof(f508,plain,(
% 1.21/0.53    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_52)),
% 1.21/0.53    inference(subsumption_resolution,[],[f507,f87])).
% 1.21/0.53  fof(f507,plain,(
% 1.21/0.53    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_52),
% 1.21/0.53    inference(trivial_inequality_removal,[],[f506])).
% 1.21/0.53  fof(f506,plain,(
% 1.21/0.53    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_52),
% 1.21/0.53    inference(superposition,[],[f496,f65])).
% 1.21/0.53  fof(f65,plain,(
% 1.21/0.53    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f29])).
% 1.21/0.53  fof(f496,plain,(
% 1.21/0.53    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | spl3_52),
% 1.21/0.53    inference(avatar_component_clause,[],[f494])).
% 1.21/0.53  fof(f484,plain,(
% 1.21/0.53    spl3_50 | ~spl3_27 | ~spl3_37),
% 1.21/0.53    inference(avatar_split_clause,[],[f379,f357,f264,f481])).
% 1.21/0.53  fof(f264,plain,(
% 1.21/0.53    spl3_27 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.21/0.53  fof(f379,plain,(
% 1.21/0.53    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_27 | ~spl3_37)),
% 1.21/0.53    inference(superposition,[],[f265,f359])).
% 1.21/0.53  fof(f265,plain,(
% 1.21/0.53    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_27),
% 1.21/0.53    inference(avatar_component_clause,[],[f264])).
% 1.21/0.53  fof(f463,plain,(
% 1.21/0.53    spl3_47 | ~spl3_31 | ~spl3_37),
% 1.21/0.53    inference(avatar_split_clause,[],[f457,f357,f297,f460])).
% 1.21/0.53  fof(f460,plain,(
% 1.21/0.53    spl3_47 <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 1.21/0.53  fof(f457,plain,(
% 1.21/0.53    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_31 | ~spl3_37)),
% 1.21/0.53    inference(forward_demodulation,[],[f306,f359])).
% 1.21/0.53  fof(f306,plain,(
% 1.21/0.53    k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_31),
% 1.21/0.53    inference(resolution,[],[f299,f75])).
% 1.21/0.53  fof(f75,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f40])).
% 1.21/0.53  fof(f40,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.53    inference(ennf_transformation,[],[f10])).
% 1.21/0.53  fof(f10,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.21/0.53  fof(f434,plain,(
% 1.21/0.53    spl3_45 | ~spl3_13 | ~spl3_22 | ~spl3_37),
% 1.21/0.53    inference(avatar_split_clause,[],[f404,f357,f224,f161,f431])).
% 1.21/0.53  fof(f161,plain,(
% 1.21/0.53    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.21/0.53  fof(f224,plain,(
% 1.21/0.53    spl3_22 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.21/0.53  fof(f404,plain,(
% 1.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_22 | ~spl3_37)),
% 1.21/0.53    inference(forward_demodulation,[],[f244,f359])).
% 1.21/0.53  fof(f244,plain,(
% 1.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_22)),
% 1.21/0.53    inference(superposition,[],[f163,f226])).
% 1.21/0.53  fof(f226,plain,(
% 1.21/0.53    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_22),
% 1.21/0.53    inference(avatar_component_clause,[],[f224])).
% 1.21/0.53  fof(f163,plain,(
% 1.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 1.21/0.53    inference(avatar_component_clause,[],[f161])).
% 1.21/0.53  fof(f427,plain,(
% 1.21/0.53    ~spl3_1 | ~spl3_28 | spl3_44),
% 1.21/0.53    inference(avatar_contradiction_clause,[],[f426])).
% 1.21/0.53  fof(f426,plain,(
% 1.21/0.53    $false | (~spl3_1 | ~spl3_28 | spl3_44)),
% 1.21/0.53    inference(subsumption_resolution,[],[f425,f273])).
% 1.21/0.53  fof(f425,plain,(
% 1.21/0.53    ~v1_relat_1(sK2) | (~spl3_1 | spl3_44)),
% 1.21/0.53    inference(subsumption_resolution,[],[f422,f87])).
% 1.21/0.53  fof(f422,plain,(
% 1.21/0.53    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_44),
% 1.21/0.53    inference(resolution,[],[f419,f63])).
% 1.21/0.53  fof(f63,plain,(
% 1.21/0.53    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f27])).
% 1.21/0.53  fof(f419,plain,(
% 1.21/0.53    ~v1_funct_1(k2_funct_1(sK2)) | spl3_44),
% 1.21/0.53    inference(avatar_component_clause,[],[f417])).
% 1.21/0.53  fof(f360,plain,(
% 1.21/0.53    spl3_37 | ~spl3_17 | ~spl3_26 | ~spl3_28),
% 1.21/0.53    inference(avatar_split_clause,[],[f355,f272,f260,f200,f357])).
% 1.21/0.53  fof(f200,plain,(
% 1.21/0.53    spl3_17 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.21/0.53  fof(f260,plain,(
% 1.21/0.53    spl3_26 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.21/0.53  fof(f355,plain,(
% 1.21/0.53    k1_relat_1(sK2) = k2_struct_0(sK0) | (~spl3_17 | ~spl3_26 | ~spl3_28)),
% 1.21/0.53    inference(subsumption_resolution,[],[f270,f273])).
% 1.21/0.53  fof(f270,plain,(
% 1.21/0.53    k1_relat_1(sK2) = k2_struct_0(sK0) | ~v1_relat_1(sK2) | (~spl3_17 | ~spl3_26)),
% 1.21/0.53    inference(subsumption_resolution,[],[f269,f202])).
% 1.21/0.53  fof(f202,plain,(
% 1.21/0.53    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_17),
% 1.21/0.53    inference(avatar_component_clause,[],[f200])).
% 1.21/0.53  fof(f269,plain,(
% 1.21/0.53    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k1_relat_1(sK2) = k2_struct_0(sK0) | ~v1_relat_1(sK2) | ~spl3_26),
% 1.21/0.53    inference(resolution,[],[f262,f74])).
% 1.21/0.53  fof(f74,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f39])).
% 1.21/0.53  fof(f39,plain,(
% 1.21/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.21/0.53    inference(flattening,[],[f38])).
% 1.21/0.53  fof(f38,plain,(
% 1.21/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.21/0.53    inference(ennf_transformation,[],[f12])).
% 1.21/0.53  fof(f12,axiom,(
% 1.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 1.21/0.53  fof(f262,plain,(
% 1.21/0.53    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_26),
% 1.21/0.53    inference(avatar_component_clause,[],[f260])).
% 1.21/0.53  fof(f354,plain,(
% 1.21/0.53    spl3_35 | spl3_36 | ~spl3_1 | ~spl3_13 | ~spl3_22 | ~spl3_27),
% 1.21/0.53    inference(avatar_split_clause,[],[f346,f264,f224,f161,f85,f351,f348])).
% 1.21/0.53  fof(f351,plain,(
% 1.21/0.53    spl3_36 <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.21/0.53  fof(f346,plain,(
% 1.21/0.53    ( ! [X0] : (r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0)) ) | (~spl3_1 | ~spl3_13 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(forward_demodulation,[],[f345,f226])).
% 1.21/0.53  fof(f345,plain,(
% 1.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(forward_demodulation,[],[f344,f226])).
% 1.21/0.53  fof(f344,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_funct_2(X0,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(forward_demodulation,[],[f343,f226])).
% 1.21/0.53  fof(f343,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(subsumption_resolution,[],[f342,f265])).
% 1.21/0.53  fof(f342,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13 | ~spl3_22)),
% 1.21/0.53    inference(forward_demodulation,[],[f190,f226])).
% 1.21/0.53  fof(f190,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | (~spl3_1 | ~spl3_13)),
% 1.21/0.53    inference(subsumption_resolution,[],[f181,f87])).
% 1.21/0.53  fof(f181,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)) ) | ~spl3_13),
% 1.21/0.53    inference(resolution,[],[f163,f82])).
% 1.21/0.53  fof(f82,plain,(
% 1.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f47])).
% 1.21/0.53  fof(f47,plain,(
% 1.21/0.53    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.21/0.53    inference(flattening,[],[f46])).
% 1.21/0.53  fof(f46,plain,(
% 1.21/0.53    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.21/0.53    inference(ennf_transformation,[],[f13])).
% 1.21/0.53  fof(f13,axiom,(
% 1.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 1.21/0.53  fof(f341,plain,(
% 1.21/0.53    spl3_34 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_22 | ~spl3_27),
% 1.21/0.53    inference(avatar_split_clause,[],[f331,f264,f224,f220,f161,f90,f85,f338])).
% 1.21/0.53  fof(f338,plain,(
% 1.21/0.53    spl3_34 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.21/0.53  fof(f220,plain,(
% 1.21/0.53    spl3_21 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.21/0.53  fof(f331,plain,(
% 1.21/0.53    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(forward_demodulation,[],[f330,f226])).
% 1.21/0.53  fof(f330,plain,(
% 1.21/0.53    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(subsumption_resolution,[],[f329,f222])).
% 1.21/0.53  fof(f222,plain,(
% 1.21/0.53    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_21),
% 1.21/0.53    inference(avatar_component_clause,[],[f220])).
% 1.21/0.53  fof(f329,plain,(
% 1.21/0.53    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(forward_demodulation,[],[f328,f226])).
% 1.21/0.53  fof(f328,plain,(
% 1.21/0.53    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(subsumption_resolution,[],[f327,f265])).
% 1.21/0.53  fof(f327,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_22)),
% 1.21/0.53    inference(forward_demodulation,[],[f189,f226])).
% 1.21/0.53  fof(f189,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 1.21/0.53    inference(subsumption_resolution,[],[f188,f92])).
% 1.21/0.53  fof(f188,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_13)),
% 1.21/0.53    inference(subsumption_resolution,[],[f180,f87])).
% 1.21/0.53  fof(f180,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 1.21/0.53    inference(resolution,[],[f163,f81])).
% 1.21/0.53  fof(f303,plain,(
% 1.21/0.53    ~spl3_13 | spl3_28),
% 1.21/0.53    inference(avatar_contradiction_clause,[],[f302])).
% 1.21/0.53  fof(f302,plain,(
% 1.21/0.53    $false | (~spl3_13 | spl3_28)),
% 1.21/0.53    inference(subsumption_resolution,[],[f301,f71])).
% 1.21/0.53  fof(f71,plain,(
% 1.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f2])).
% 1.21/0.53  fof(f2,axiom,(
% 1.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.21/0.53  fof(f301,plain,(
% 1.21/0.53    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_13 | spl3_28)),
% 1.21/0.53    inference(resolution,[],[f279,f163])).
% 1.21/0.53  fof(f279,plain,(
% 1.21/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_28),
% 1.21/0.53    inference(resolution,[],[f274,f60])).
% 1.21/0.53  fof(f60,plain,(
% 1.21/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f23])).
% 1.21/0.53  fof(f23,plain,(
% 1.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.21/0.53    inference(ennf_transformation,[],[f1])).
% 1.21/0.53  fof(f1,axiom,(
% 1.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.21/0.53  fof(f274,plain,(
% 1.21/0.53    ~v1_relat_1(sK2) | spl3_28),
% 1.21/0.53    inference(avatar_component_clause,[],[f272])).
% 1.21/0.53  fof(f300,plain,(
% 1.21/0.53    spl3_31 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_22 | ~spl3_27),
% 1.21/0.53    inference(avatar_split_clause,[],[f295,f264,f224,f220,f161,f90,f85,f297])).
% 1.21/0.53  fof(f295,plain,(
% 1.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(forward_demodulation,[],[f294,f226])).
% 1.21/0.53  fof(f294,plain,(
% 1.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(subsumption_resolution,[],[f293,f222])).
% 1.21/0.53  fof(f293,plain,(
% 1.21/0.53    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(forward_demodulation,[],[f292,f226])).
% 1.21/0.53  fof(f292,plain,(
% 1.21/0.53    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(subsumption_resolution,[],[f291,f265])).
% 1.21/0.53  fof(f291,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_22)),
% 1.21/0.53    inference(forward_demodulation,[],[f187,f226])).
% 1.21/0.53  fof(f187,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 1.21/0.53    inference(subsumption_resolution,[],[f186,f92])).
% 1.21/0.53  fof(f186,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_13)),
% 1.21/0.53    inference(subsumption_resolution,[],[f179,f87])).
% 1.21/0.53  fof(f179,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl3_13),
% 1.21/0.53    inference(resolution,[],[f163,f80])).
% 1.21/0.53  fof(f80,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f43])).
% 1.21/0.53  fof(f43,plain,(
% 1.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.21/0.53    inference(flattening,[],[f42])).
% 1.21/0.53  fof(f42,plain,(
% 1.21/0.53    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.21/0.53    inference(ennf_transformation,[],[f14])).
% 1.21/0.53  fof(f14,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.21/0.53  fof(f290,plain,(
% 1.21/0.53    spl3_30 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_22 | ~spl3_27),
% 1.21/0.53    inference(avatar_split_clause,[],[f284,f264,f224,f220,f161,f90,f85,f287])).
% 1.21/0.53  fof(f284,plain,(
% 1.21/0.53    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(forward_demodulation,[],[f283,f226])).
% 1.21/0.53  fof(f283,plain,(
% 1.21/0.53    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_21 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(subsumption_resolution,[],[f282,f222])).
% 1.21/0.53  fof(f282,plain,(
% 1.21/0.53    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(forward_demodulation,[],[f281,f226])).
% 1.21/0.53  % (9037)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.21/0.53  fof(f281,plain,(
% 1.21/0.53    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_22 | ~spl3_27)),
% 1.21/0.53    inference(subsumption_resolution,[],[f280,f265])).
% 1.21/0.53  fof(f280,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_22)),
% 1.21/0.53    inference(forward_demodulation,[],[f185,f226])).
% 1.21/0.53  fof(f185,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 1.21/0.53    inference(subsumption_resolution,[],[f184,f92])).
% 1.21/0.53  fof(f184,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_13)),
% 1.21/0.53    inference(subsumption_resolution,[],[f178,f87])).
% 1.21/0.53  fof(f178,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~spl3_13),
% 1.21/0.53    inference(resolution,[],[f163,f79])).
% 1.21/0.53  fof(f79,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f43])).
% 1.21/0.53  fof(f268,plain,(
% 1.21/0.53    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | u1_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.21/0.53  fof(f267,plain,(
% 1.21/0.53    spl3_26 | ~spl3_27 | ~spl3_1 | spl3_12 | ~spl3_13 | ~spl3_22),
% 1.21/0.53    inference(avatar_split_clause,[],[f258,f224,f161,f154,f85,f264,f260])).
% 1.21/0.53  fof(f154,plain,(
% 1.21/0.53    spl3_12 <=> v1_xboole_0(k2_struct_0(sK1))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.21/0.53  fof(f258,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | spl3_12 | ~spl3_13 | ~spl3_22)),
% 1.21/0.53    inference(forward_demodulation,[],[f183,f226])).
% 1.21/0.53  fof(f183,plain,(
% 1.21/0.53    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | spl3_12 | ~spl3_13)),
% 1.21/0.53    inference(subsumption_resolution,[],[f182,f87])).
% 1.21/0.53  fof(f182,plain,(
% 1.21/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (spl3_12 | ~spl3_13)),
% 1.21/0.53    inference(subsumption_resolution,[],[f174,f156])).
% 1.21/0.53  fof(f156,plain,(
% 1.21/0.53    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_12),
% 1.21/0.53    inference(avatar_component_clause,[],[f154])).
% 1.21/0.53  fof(f174,plain,(
% 1.21/0.53    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 1.21/0.53    inference(resolution,[],[f163,f72])).
% 1.21/0.53  fof(f72,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f37])).
% 1.21/0.53  fof(f37,plain,(
% 1.21/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.21/0.53    inference(flattening,[],[f36])).
% 1.21/0.53  fof(f36,plain,(
% 1.21/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f11])).
% 1.21/0.53  fof(f11,axiom,(
% 1.21/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.21/0.53  fof(f234,plain,(
% 1.21/0.53    u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.21/0.53  fof(f233,plain,(
% 1.21/0.53    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.21/0.53  fof(f214,plain,(
% 1.21/0.53    spl3_19 | ~spl3_13),
% 1.21/0.53    inference(avatar_split_clause,[],[f175,f161,f211])).
% 1.21/0.53  fof(f211,plain,(
% 1.21/0.53    spl3_19 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.21/0.53  fof(f175,plain,(
% 1.21/0.53    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 1.21/0.53    inference(resolution,[],[f163,f75])).
% 1.21/0.53  fof(f203,plain,(
% 1.21/0.53    spl3_17 | ~spl3_13),
% 1.21/0.53    inference(avatar_split_clause,[],[f176,f161,f200])).
% 1.21/0.53  fof(f176,plain,(
% 1.21/0.53    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 1.21/0.53    inference(resolution,[],[f163,f76])).
% 1.21/0.53  fof(f76,plain,(
% 1.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f41])).
% 1.21/0.53  fof(f41,plain,(
% 1.21/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.21/0.53    inference(ennf_transformation,[],[f9])).
% 1.21/0.53  fof(f9,axiom,(
% 1.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.21/0.53  fof(f198,plain,(
% 1.21/0.53    ~spl3_16 | ~spl3_7 | ~spl3_9),
% 1.21/0.53    inference(avatar_split_clause,[],[f193,f129,f119,f195])).
% 1.21/0.53  % (9024)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.53  fof(f195,plain,(
% 1.21/0.53    spl3_16 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.21/0.53  fof(f119,plain,(
% 1.21/0.53    spl3_7 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.21/0.53  fof(f129,plain,(
% 1.21/0.53    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.21/0.53  % (9041)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.21/0.53  fof(f193,plain,(
% 1.21/0.53    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_7 | ~spl3_9)),
% 1.21/0.53    inference(forward_demodulation,[],[f192,f131])).
% 1.21/0.53  fof(f131,plain,(
% 1.21/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 1.21/0.53    inference(avatar_component_clause,[],[f129])).
% 1.21/0.53  fof(f192,plain,(
% 1.21/0.53    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~spl3_7),
% 1.21/0.53    inference(forward_demodulation,[],[f53,f121])).
% 1.21/0.53  fof(f121,plain,(
% 1.21/0.53    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 1.21/0.53    inference(avatar_component_clause,[],[f119])).
% 1.21/0.53  fof(f53,plain,(
% 1.21/0.53    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.21/0.53    inference(cnf_transformation,[],[f21])).
% 1.21/0.53  fof(f21,plain,(
% 1.21/0.53    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.21/0.53    inference(flattening,[],[f20])).
% 1.21/0.53  fof(f20,plain,(
% 1.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.21/0.53    inference(ennf_transformation,[],[f19])).
% 1.21/0.53  fof(f19,negated_conjecture,(
% 1.21/0.53    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.21/0.53    inference(negated_conjecture,[],[f18])).
% 1.21/0.53  fof(f18,conjecture,(
% 1.21/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 1.21/0.53  fof(f164,plain,(
% 1.21/0.53    spl3_13 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 1.21/0.53    inference(avatar_split_clause,[],[f152,f129,f124,f119,f161])).
% 1.21/0.53  fof(f124,plain,(
% 1.21/0.53    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.21/0.53  fof(f152,plain,(
% 1.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 1.21/0.53    inference(forward_demodulation,[],[f146,f131])).
% 1.21/0.53  fof(f146,plain,(
% 1.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8)),
% 1.21/0.53    inference(forward_demodulation,[],[f126,f121])).
% 1.21/0.53  fof(f126,plain,(
% 1.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 1.21/0.53    inference(avatar_component_clause,[],[f124])).
% 1.21/0.53  fof(f157,plain,(
% 1.21/0.53    ~spl3_12 | spl3_3 | ~spl3_4 | ~spl3_7),
% 1.21/0.53    inference(avatar_split_clause,[],[f145,f119,f100,f95,f154])).
% 1.21/0.53  fof(f95,plain,(
% 1.21/0.53    spl3_3 <=> v2_struct_0(sK1)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.21/0.53  fof(f100,plain,(
% 1.21/0.53    spl3_4 <=> l1_struct_0(sK1)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.21/0.53  fof(f145,plain,(
% 1.21/0.53    ~v1_xboole_0(k2_struct_0(sK1)) | (spl3_3 | ~spl3_4 | ~spl3_7)),
% 1.21/0.53    inference(subsumption_resolution,[],[f144,f97])).
% 1.21/0.53  fof(f97,plain,(
% 1.21/0.53    ~v2_struct_0(sK1) | spl3_3),
% 1.21/0.53    inference(avatar_component_clause,[],[f95])).
% 1.21/0.53  fof(f144,plain,(
% 1.21/0.53    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_7)),
% 1.21/0.53    inference(subsumption_resolution,[],[f143,f102])).
% 1.21/0.53  fof(f102,plain,(
% 1.21/0.53    l1_struct_0(sK1) | ~spl3_4),
% 1.21/0.53    inference(avatar_component_clause,[],[f100])).
% 1.21/0.53  fof(f143,plain,(
% 1.21/0.53    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_7),
% 1.21/0.53    inference(superposition,[],[f61,f121])).
% 1.21/0.53  fof(f61,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f25])).
% 1.21/0.53  fof(f25,plain,(
% 1.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.21/0.53    inference(flattening,[],[f24])).
% 1.21/0.53  fof(f24,plain,(
% 1.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.21/0.53    inference(ennf_transformation,[],[f16])).
% 1.21/0.53  fof(f16,axiom,(
% 1.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.21/0.53  fof(f137,plain,(
% 1.21/0.53    spl3_10),
% 1.21/0.53    inference(avatar_split_clause,[],[f51,f134])).
% 1.21/0.53  fof(f134,plain,(
% 1.21/0.53    spl3_10 <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.21/0.53  fof(f51,plain,(
% 1.21/0.53    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.21/0.53    inference(cnf_transformation,[],[f21])).
% 1.21/0.53  fof(f132,plain,(
% 1.21/0.53    spl3_9 | ~spl3_5),
% 1.21/0.53    inference(avatar_split_clause,[],[f112,f105,f129])).
% 1.21/0.53  fof(f105,plain,(
% 1.21/0.53    spl3_5 <=> l1_struct_0(sK0)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.21/0.53  fof(f112,plain,(
% 1.21/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 1.21/0.53    inference(resolution,[],[f107,f59])).
% 1.21/0.53  fof(f59,plain,(
% 1.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f22])).
% 1.21/0.53  fof(f22,plain,(
% 1.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.21/0.53    inference(ennf_transformation,[],[f15])).
% 1.21/0.53  fof(f15,axiom,(
% 1.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.21/0.53  fof(f107,plain,(
% 1.21/0.53    l1_struct_0(sK0) | ~spl3_5),
% 1.21/0.53    inference(avatar_component_clause,[],[f105])).
% 1.21/0.53  fof(f127,plain,(
% 1.21/0.53    spl3_8),
% 1.21/0.53    inference(avatar_split_clause,[],[f50,f124])).
% 1.21/0.53  fof(f50,plain,(
% 1.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.21/0.53    inference(cnf_transformation,[],[f21])).
% 1.21/0.53  fof(f122,plain,(
% 1.21/0.53    spl3_7 | ~spl3_4),
% 1.21/0.53    inference(avatar_split_clause,[],[f111,f100,f119])).
% 1.21/0.53  fof(f111,plain,(
% 1.21/0.53    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_4),
% 1.21/0.53    inference(resolution,[],[f102,f59])).
% 1.21/0.53  fof(f117,plain,(
% 1.21/0.53    spl3_6),
% 1.21/0.53    inference(avatar_split_clause,[],[f49,f114])).
% 1.21/0.53  fof(f114,plain,(
% 1.21/0.53    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.21/0.53  fof(f49,plain,(
% 1.21/0.53    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.21/0.53    inference(cnf_transformation,[],[f21])).
% 1.21/0.53  fof(f108,plain,(
% 1.21/0.53    spl3_5),
% 1.21/0.53    inference(avatar_split_clause,[],[f56,f105])).
% 1.21/0.53  fof(f56,plain,(
% 1.21/0.53    l1_struct_0(sK0)),
% 1.21/0.53    inference(cnf_transformation,[],[f21])).
% 1.21/0.53  fof(f103,plain,(
% 1.21/0.53    spl3_4),
% 1.21/0.53    inference(avatar_split_clause,[],[f55,f100])).
% 1.21/0.53  fof(f55,plain,(
% 1.21/0.53    l1_struct_0(sK1)),
% 1.21/0.53    inference(cnf_transformation,[],[f21])).
% 1.21/0.53  fof(f98,plain,(
% 1.21/0.53    ~spl3_3),
% 1.21/0.53    inference(avatar_split_clause,[],[f54,f95])).
% 1.21/0.53  fof(f54,plain,(
% 1.21/0.53    ~v2_struct_0(sK1)),
% 1.21/0.53    inference(cnf_transformation,[],[f21])).
% 1.21/0.53  fof(f93,plain,(
% 1.21/0.53    spl3_2),
% 1.21/0.53    inference(avatar_split_clause,[],[f52,f90])).
% 1.21/0.53  fof(f52,plain,(
% 1.21/0.53    v2_funct_1(sK2)),
% 1.21/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  fof(f88,plain,(
% 1.34/0.53    spl3_1),
% 1.34/0.53    inference(avatar_split_clause,[],[f48,f85])).
% 1.34/0.53  fof(f48,plain,(
% 1.34/0.53    v1_funct_1(sK2)),
% 1.34/0.53    inference(cnf_transformation,[],[f21])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (9026)------------------------------
% 1.34/0.53  % (9026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (9026)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (9026)Memory used [KB]: 11129
% 1.34/0.53  % (9026)Time elapsed: 0.093 s
% 1.34/0.53  % (9026)------------------------------
% 1.34/0.53  % (9026)------------------------------
% 1.34/0.53  % (9036)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.34/0.53  % (9022)Success in time 0.167 s
%------------------------------------------------------------------------------
