%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:28 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  299 ( 620 expanded)
%              Number of leaves         :   74 ( 295 expanded)
%              Depth                    :    9
%              Number of atoms          : 1191 (2508 expanded)
%              Number of equality atoms :  164 ( 305 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f954,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f122,f127,f132,f137,f142,f147,f152,f181,f186,f195,f200,f204,f209,f215,f222,f229,f239,f244,f267,f272,f317,f341,f356,f372,f377,f381,f390,f412,f427,f445,f448,f521,f536,f553,f559,f562,f601,f610,f627,f630,f662,f675,f693,f741,f748,f882,f883,f946,f953])).

fof(f953,plain,
    ( ~ spl3_52
    | ~ spl3_29
    | ~ spl3_3
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_51
    | ~ spl3_63
    | ~ spl3_109 ),
    inference(avatar_split_clause,[],[f951,f944,f533,f430,f192,f114,f124,f299,f434])).

fof(f434,plain,
    ( spl3_52
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f299,plain,
    ( spl3_29
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f124,plain,
    ( spl3_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f114,plain,
    ( spl3_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f192,plain,
    ( spl3_14
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f430,plain,
    ( spl3_51
  <=> sK0 = k2_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f533,plain,
    ( spl3_63
  <=> sK1 = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f944,plain,
    ( spl3_109
  <=> ! [X0] :
        ( k2_funct_1(X0) != k2_funct_1(k5_relat_1(sK2,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_relat_1(k2_funct_1(X0)) != sK0
        | ~ v1_funct_1(k2_funct_1(X0))
        | ~ v1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).

fof(f951,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_51
    | ~ spl3_63
    | ~ spl3_109 ),
    inference(trivial_inequality_removal,[],[f950])).

fof(f950,plain,
    ( sK0 != sK0
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_51
    | ~ spl3_63
    | ~ spl3_109 ),
    inference(forward_demodulation,[],[f949,f431])).

fof(f431,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK1))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f430])).

fof(f949,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_63
    | ~ spl3_109 ),
    inference(trivial_inequality_removal,[],[f947])).

fof(f947,plain,
    ( k2_funct_1(sK1) != k2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | sK0 != k2_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl3_63
    | ~ spl3_109 ),
    inference(superposition,[],[f945,f535])).

fof(f535,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f533])).

fof(f945,plain,
    ( ! [X0] :
        ( k2_funct_1(X0) != k2_funct_1(k5_relat_1(sK2,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_relat_1(k2_funct_1(X0)) != sK0
        | ~ v1_funct_1(k2_funct_1(X0))
        | ~ v1_relat_1(k2_funct_1(X0)) )
    | ~ spl3_109 ),
    inference(avatar_component_clause,[],[f944])).

fof(f946,plain,
    ( ~ spl3_16
    | ~ spl3_2
    | ~ spl3_35
    | spl3_109
    | ~ spl3_101 ),
    inference(avatar_split_clause,[],[f884,f880,f944,f334,f119,f206])).

fof(f206,plain,
    ( spl3_16
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f119,plain,
    ( spl3_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f334,plain,
    ( spl3_35
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f880,plain,
    ( spl3_101
  <=> ! [X0] :
        ( k5_relat_1(X0,k2_funct_1(sK2)) != X0
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_relat_1(X0) != sK0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).

fof(f884,plain,
    ( ! [X0] :
        ( k2_funct_1(X0) != k2_funct_1(k5_relat_1(sK2,X0))
        | ~ v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(k2_funct_1(X0))
        | k2_relat_1(k2_funct_1(X0)) != sK0
        | ~ v2_funct_1(X0)
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_101 ),
    inference(superposition,[],[f881,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

fof(f881,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k2_funct_1(sK2)) != X0
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_relat_1(X0) != sK0 )
    | ~ spl3_101 ),
    inference(avatar_component_clause,[],[f880])).

fof(f883,plain,
    ( sK2 != k6_relat_1(sK0)
    | r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f882,plain,
    ( ~ spl3_70
    | ~ spl3_34
    | spl3_101
    | spl3_76
    | ~ spl3_88 ),
    inference(avatar_split_clause,[],[f754,f745,f672,f880,f330,f616])).

fof(f616,plain,
    ( spl3_70
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f330,plain,
    ( spl3_34
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f672,plain,
    ( spl3_76
  <=> k6_relat_1(sK0) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f745,plain,
    ( spl3_88
  <=> sK0 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).

fof(f754,plain,
    ( ! [X0] :
        ( k6_relat_1(sK0) = k2_funct_1(sK2)
        | k5_relat_1(X0,k2_funct_1(sK2)) != X0
        | k2_relat_1(X0) != sK0
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_88 ),
    inference(superposition,[],[f88,f747])).

fof(f747,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_88 ),
    inference(avatar_component_clause,[],[f745])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f748,plain,
    ( ~ spl3_79
    | spl3_88
    | ~ spl3_87 ),
    inference(avatar_split_clause,[],[f742,f738,f745,f690])).

fof(f690,plain,
    ( spl3_79
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f738,plain,
    ( spl3_87
  <=> sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f742,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_87 ),
    inference(superposition,[],[f740,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f740,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK2))
    | ~ spl3_87 ),
    inference(avatar_component_clause,[],[f738])).

fof(f741,plain,
    ( ~ spl3_34
    | ~ spl3_68
    | spl3_87
    | ~ spl3_79 ),
    inference(avatar_split_clause,[],[f696,f690,f738,f607,f330])).

fof(f607,plain,
    ( spl3_68
  <=> v1_funct_2(k2_funct_1(sK2),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f696,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_79 ),
    inference(resolution,[],[f692,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f692,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_79 ),
    inference(avatar_component_clause,[],[f690])).

fof(f693,plain,
    ( ~ spl3_16
    | ~ spl3_2
    | ~ spl3_35
    | spl3_79
    | ~ spl3_41
    | ~ spl3_75 ),
    inference(avatar_split_clause,[],[f670,f659,f369,f690,f334,f119,f206])).

fof(f369,plain,
    ( spl3_41
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f659,plain,
    ( spl3_75
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f670,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_41
    | ~ spl3_75 ),
    inference(forward_demodulation,[],[f669,f370])).

fof(f370,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f369])).

fof(f669,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),sK0)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_75 ),
    inference(superposition,[],[f661,f81])).

fof(f81,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f661,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f659])).

fof(f675,plain,
    ( ~ spl3_16
    | ~ spl3_2
    | ~ spl3_35
    | ~ spl3_34
    | ~ spl3_70
    | ~ spl3_76
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f645,f612,f406,f369,f672,f616,f330,f334,f119,f206])).

fof(f406,plain,
    ( spl3_47
  <=> ! [X0] :
        ( k5_relat_1(X0,sK2) != X0
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_relat_1(X0) != sK0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f612,plain,
    ( spl3_69
  <=> sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f645,plain,
    ( k6_relat_1(sK0) != k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_69 ),
    inference(trivial_inequality_removal,[],[f644])).

fof(f644,plain,
    ( sK0 != sK0
    | k6_relat_1(sK0) != k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_41
    | ~ spl3_47
    | ~ spl3_69 ),
    inference(forward_demodulation,[],[f643,f613])).

fof(f613,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f612])).

fof(f643,plain,
    ( k6_relat_1(sK0) != k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK0 != k2_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_41
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f413,f370])).

fof(f413,plain,
    ( k2_funct_1(sK2) != k6_relat_1(k2_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK0 != k2_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_47 ),
    inference(superposition,[],[f407,f84])).

fof(f84,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f407,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,sK2) != X0
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_relat_1(X0) != sK0 )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f406])).

fof(f662,plain,
    ( ~ spl3_70
    | ~ spl3_34
    | spl3_75
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f638,f612,f659,f330,f616])).

fof(f638,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_69 ),
    inference(superposition,[],[f78,f613])).

fof(f78,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f630,plain,
    ( ~ spl3_2
    | ~ spl3_16
    | spl3_70 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_16
    | spl3_70 ),
    inference(unit_resulting_resolution,[],[f208,f121,f618,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f618,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_70 ),
    inference(avatar_component_clause,[],[f616])).

fof(f121,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f208,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f206])).

fof(f627,plain,
    ( ~ spl3_16
    | ~ spl3_2
    | ~ spl3_35
    | ~ spl3_21
    | spl3_69 ),
    inference(avatar_split_clause,[],[f626,f612,f241,f334,f119,f206])).

fof(f241,plain,
    ( spl3_21
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f626,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_21
    | spl3_69 ),
    inference(trivial_inequality_removal,[],[f625])).

fof(f625,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_21
    | spl3_69 ),
    inference(forward_demodulation,[],[f624,f243])).

fof(f243,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f241])).

fof(f624,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_69 ),
    inference(superposition,[],[f614,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f614,plain,
    ( sK0 != k2_relat_1(k2_funct_1(sK2))
    | spl3_69 ),
    inference(avatar_component_clause,[],[f612])).

fof(f610,plain,
    ( spl3_68
    | ~ spl3_41
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f605,f424,f369,f607])).

fof(f424,plain,
    ( spl3_50
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f605,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK0,sK0)
    | ~ spl3_41
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f426,f370])).

fof(f426,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0)
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f424])).

fof(f601,plain,
    ( spl3_35
    | ~ spl3_2
    | ~ spl3_16
    | ~ spl3_3
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f600,f533,f369,f354,f124,f206,f119,f334])).

fof(f354,plain,
    ( spl3_38
  <=> ! [X1] :
        ( k2_relat_1(X1) != sK0
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,sK1))
        | v2_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f600,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_63 ),
    inference(trivial_inequality_removal,[],[f599])).

fof(f599,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ spl3_38
    | ~ spl3_41
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f539,f370])).

fof(f539,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK0 != k2_relat_1(sK2)
    | v2_funct_1(sK2)
    | ~ spl3_38
    | ~ spl3_63 ),
    inference(superposition,[],[f355,f535])).

fof(f355,plain,
    ( ! [X1] :
        ( ~ v2_funct_1(k5_relat_1(X1,sK1))
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k2_relat_1(X1) != sK0
        | v2_funct_1(X1) )
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f354])).

fof(f562,plain,
    ( ~ spl3_11
    | ~ spl3_16
    | spl3_65 ),
    inference(avatar_contradiction_clause,[],[f560])).

fof(f560,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_16
    | spl3_65 ),
    inference(unit_resulting_resolution,[],[f208,f180,f558,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f558,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK0)
    | spl3_65 ),
    inference(avatar_component_clause,[],[f556])).

fof(f556,plain,
    ( spl3_65
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f180,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_11
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f559,plain,
    ( ~ spl3_65
    | spl3_41
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f554,f550,f369,f556])).

fof(f550,plain,
    ( spl3_64
  <=> r1_tarski(sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f554,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl3_64 ),
    inference(resolution,[],[f552,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f552,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f550])).

fof(f553,plain,
    ( ~ spl3_14
    | ~ spl3_1
    | ~ spl3_16
    | ~ spl3_2
    | ~ spl3_3
    | spl3_64
    | ~ spl3_19
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f542,f533,f226,f550,f124,f119,f206,f114,f192])).

fof(f226,plain,
    ( spl3_19
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f542,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_19
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f541,f228])).

fof(f228,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f226])).

fof(f541,plain,
    ( ~ v2_funct_1(sK1)
    | r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_63 ),
    inference(trivial_inequality_removal,[],[f540])).

fof(f540,plain,
    ( k2_relat_1(sK1) != k2_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_63 ),
    inference(superposition,[],[f89,f535])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
      | ~ v2_funct_1(X0)
      | r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
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
         => ( ( v2_funct_1(X0)
              & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

fof(f536,plain,
    ( ~ spl3_2
    | ~ spl3_7
    | ~ spl3_1
    | ~ spl3_6
    | spl3_63
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f523,f518,f533,f139,f114,f144,f119])).

fof(f144,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f139,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f518,plain,
    ( spl3_62
  <=> sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f523,plain,
    ( sK1 = k5_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl3_62 ),
    inference(superposition,[],[f520,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f520,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f518])).

fof(f521,plain,
    ( ~ spl3_2
    | ~ spl3_7
    | ~ spl3_1
    | ~ spl3_6
    | spl3_62
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f461,f197,f139,f518,f139,f114,f144,f119])).

fof(f197,plain,
    ( spl3_15
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f461,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(resolution,[],[f246,f199])).

fof(f199,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f197])).

fof(f246,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,X1,X2,sK0,X3,X4),sK1)
        | sK1 = k1_partfun1(sK0,X1,X2,sK0,X3,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X3) )
    | ~ spl3_6 ),
    inference(resolution,[],[f154,f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | sK1 = X0
        | ~ r2_relset_1(sK0,sK0,X0,sK1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f141,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f141,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f448,plain,
    ( ~ spl3_1
    | ~ spl3_14
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_14
    | spl3_52 ),
    inference(unit_resulting_resolution,[],[f194,f116,f436,f79])).

fof(f436,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f434])).

fof(f116,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f194,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f192])).

fof(f445,plain,
    ( ~ spl3_14
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_19
    | spl3_51 ),
    inference(avatar_split_clause,[],[f444,f430,f226,f124,f114,f192])).

fof(f444,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_19
    | spl3_51 ),
    inference(trivial_inequality_removal,[],[f443])).

fof(f443,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_19
    | spl3_51 ),
    inference(forward_demodulation,[],[f442,f228])).

fof(f442,plain,
    ( sK0 != k1_relat_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_51 ),
    inference(superposition,[],[f432,f82])).

fof(f432,plain,
    ( sK0 != k2_relat_1(k2_funct_1(sK1))
    | spl3_51 ),
    inference(avatar_component_clause,[],[f430])).

fof(f427,plain,
    ( ~ spl3_2
    | ~ spl3_24
    | spl3_50
    | ~ spl3_35
    | ~ spl3_32
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f422,f383,f314,f334,f424,f264,f119])).

fof(f264,plain,
    ( spl3_24
  <=> v1_funct_2(sK2,sK0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f314,plain,
    ( spl3_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f383,plain,
    ( spl3_43
  <=> k2_relat_1(sK2) = k2_relset_1(sK0,k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f422,plain,
    ( ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0)
    | ~ v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_32
    | ~ spl3_43 ),
    inference(trivial_inequality_removal,[],[f421])).

fof(f421,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0)
    | ~ v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_32
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f321,f384])).

fof(f384,plain,
    ( k2_relat_1(sK2) = k2_relset_1(sK0,k2_relat_1(sK2),sK2)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f383])).

fof(f321,plain,
    ( k2_relat_1(sK2) != k2_relset_1(sK0,k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0)
    | ~ v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_32 ),
    inference(resolution,[],[f316,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f316,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f314])).

fof(f412,plain,
    ( ~ spl3_16
    | ~ spl3_2
    | spl3_47
    | spl3_48
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f249,f241,f409,f406,f119,f206])).

fof(f409,plain,
    ( spl3_48
  <=> sK2 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f249,plain,
    ( ! [X0] :
        ( sK2 = k6_relat_1(sK0)
        | k5_relat_1(X0,sK2) != X0
        | k2_relat_1(X0) != sK0
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_21 ),
    inference(superposition,[],[f88,f243])).

fof(f390,plain,
    ( ~ spl3_32
    | spl3_43 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | ~ spl3_32
    | spl3_43 ),
    inference(unit_resulting_resolution,[],[f316,f385,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f385,plain,
    ( k2_relat_1(sK2) != k2_relset_1(sK0,k2_relat_1(sK2),sK2)
    | spl3_43 ),
    inference(avatar_component_clause,[],[f383])).

fof(f381,plain,
    ( ~ spl3_25
    | spl3_42 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl3_25
    | spl3_42 ),
    inference(unit_resulting_resolution,[],[f271,f376,f98])).

fof(f376,plain,
    ( k2_relat_1(sK1) != k2_relset_1(sK0,k2_relat_1(sK1),sK1)
    | spl3_42 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl3_42
  <=> k2_relat_1(sK1) = k2_relset_1(sK0,k2_relat_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f271,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl3_25
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f377,plain,
    ( ~ spl3_1
    | ~ spl3_20
    | spl3_29
    | ~ spl3_3
    | ~ spl3_42
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f279,f269,f374,f124,f299,f236,f114])).

fof(f236,plain,
    ( spl3_20
  <=> v1_funct_2(sK1,sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f279,plain,
    ( k2_relat_1(sK1) != k2_relset_1(sK0,k2_relat_1(sK1),sK1)
    | ~ v2_funct_1(sK1)
    | v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_2(sK1,sK0,k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ spl3_25 ),
    inference(resolution,[],[f271,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f372,plain,
    ( ~ spl3_7
    | ~ spl3_41
    | spl3_36 ),
    inference(avatar_split_clause,[],[f367,f338,f369,f144])).

fof(f338,plain,
    ( spl3_36
  <=> sK0 = k2_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f367,plain,
    ( sK0 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_36 ),
    inference(superposition,[],[f340,f98])).

fof(f340,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK2)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f338])).

fof(f356,plain,
    ( ~ spl3_14
    | ~ spl3_1
    | spl3_38
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f231,f226,f354,f114,f192])).

fof(f231,plain,
    ( ! [X1] :
        ( k2_relat_1(X1) != sK0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,sK1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_19 ),
    inference(superposition,[],[f86,f228])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f341,plain,
    ( ~ spl3_2
    | ~ spl3_5
    | spl3_34
    | ~ spl3_35
    | ~ spl3_36
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f173,f144,f338,f334,f330,f134,f119])).

fof(f134,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f173,plain,
    ( sK0 != k2_relset_1(sK0,sK0,sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_7 ),
    inference(resolution,[],[f146,f100])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f317,plain,
    ( ~ spl3_16
    | ~ spl3_2
    | spl3_32
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f253,f241,f314,f119,f206])).

fof(f253,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(superposition,[],[f78,f243])).

fof(f272,plain,
    ( ~ spl3_14
    | ~ spl3_1
    | spl3_25
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f234,f226,f269,f114,f192])).

fof(f234,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_19 ),
    inference(superposition,[],[f78,f228])).

fof(f267,plain,
    ( ~ spl3_16
    | ~ spl3_2
    | spl3_24
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f252,f241,f264,f119,f206])).

fof(f252,plain,
    ( v1_funct_2(sK2,sK0,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(superposition,[],[f77,f243])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f244,plain,
    ( ~ spl3_7
    | spl3_21
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f223,f219,f241,f144])).

fof(f219,plain,
    ( spl3_18
  <=> sK0 = k1_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f223,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_18 ),
    inference(superposition,[],[f221,f97])).

fof(f221,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f219])).

fof(f239,plain,
    ( ~ spl3_14
    | ~ spl3_1
    | spl3_20
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f233,f226,f236,f114,f192])).

fof(f233,plain,
    ( v1_funct_2(sK1,sK0,k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_19 ),
    inference(superposition,[],[f77,f228])).

fof(f229,plain,
    ( ~ spl3_6
    | spl3_19
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f216,f212,f226,f139])).

fof(f212,plain,
    ( spl3_17
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f216,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_17 ),
    inference(superposition,[],[f214,f97])).

fof(f214,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f212])).

fof(f222,plain,
    ( ~ spl3_2
    | ~ spl3_5
    | spl3_18
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f170,f144,f219,f134,f119])).

fof(f170,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_7 ),
    inference(resolution,[],[f146,f93])).

fof(f215,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | spl3_17
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f153,f139,f212,f129,f114])).

fof(f129,plain,
    ( spl3_4
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f153,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f141,f93])).

fof(f209,plain,
    ( ~ spl3_13
    | spl3_16
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f176,f144,f206,f188])).

fof(f188,plain,
    ( spl3_13
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f176,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl3_7 ),
    inference(resolution,[],[f146,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f204,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f90,f190])).

fof(f190,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f188])).

fof(f90,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f200,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f71,f197])).

fof(f71,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f59,f58])).

fof(f58,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & v2_funct_1(sK1)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
        & v2_funct_1(sK1)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
      & v2_funct_1(sK1)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(f195,plain,
    ( ~ spl3_13
    | spl3_14
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f159,f139,f192,f188])).

fof(f159,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl3_6 ),
    inference(resolution,[],[f141,f75])).

fof(f186,plain,
    ( spl3_12
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f172,f144,f183])).

fof(f183,plain,
    ( spl3_12
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f172,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_7 ),
    inference(resolution,[],[f146,f112])).

fof(f112,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f181,plain,
    ( spl3_11
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f175,f144,f178])).

fof(f175,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f146,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f152,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f108,f149])).

fof(f149,plain,
    ( spl3_8
  <=> r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f108,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f73,f74])).

fof(f74,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f73,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f60])).

fof(f147,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f70,f144])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f142,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f67,f139])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f137,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f69,f134])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f132,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f66,f129])).

fof(f66,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f127,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f72,f124])).

fof(f72,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f122,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f68,f119])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f117,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f65,f114])).

fof(f65,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:15:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (29204)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.48  % (29212)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.50  % (29212)Refutation not found, incomplete strategy% (29212)------------------------------
% 0.21/0.50  % (29212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29212)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29212)Memory used [KB]: 10746
% 0.21/0.50  % (29212)Time elapsed: 0.080 s
% 0.21/0.50  % (29212)------------------------------
% 0.21/0.50  % (29212)------------------------------
% 1.28/0.53  % (29213)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.28/0.53  % (29199)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.54  % (29203)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.28/0.54  % (29222)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (29224)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.28/0.54  % (29225)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.36/0.54  % (29201)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.36/0.54  % (29198)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.36/0.54  % (29197)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.36/0.55  % (29217)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.36/0.55  % (29215)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.36/0.55  % (29223)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.36/0.55  % (29200)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.36/0.55  % (29216)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.36/0.55  % (29207)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.36/0.55  % (29206)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.36/0.56  % (29196)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.36/0.56  % (29209)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.56  % (29205)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.36/0.56  % (29208)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.36/0.56  % (29220)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.36/0.57  % (29218)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.36/0.57  % (29202)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.58  % (29211)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.36/0.58  % (29214)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.58  % (29221)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.36/0.58  % (29219)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.36/0.59  % (29210)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.36/0.61  % (29206)Refutation found. Thanks to Tanya!
% 1.36/0.61  % SZS status Theorem for theBenchmark
% 1.36/0.61  % SZS output start Proof for theBenchmark
% 1.36/0.61  fof(f954,plain,(
% 1.36/0.61    $false),
% 1.36/0.61    inference(avatar_sat_refutation,[],[f117,f122,f127,f132,f137,f142,f147,f152,f181,f186,f195,f200,f204,f209,f215,f222,f229,f239,f244,f267,f272,f317,f341,f356,f372,f377,f381,f390,f412,f427,f445,f448,f521,f536,f553,f559,f562,f601,f610,f627,f630,f662,f675,f693,f741,f748,f882,f883,f946,f953])).
% 1.36/0.61  fof(f953,plain,(
% 1.36/0.61    ~spl3_52 | ~spl3_29 | ~spl3_3 | ~spl3_1 | ~spl3_14 | ~spl3_51 | ~spl3_63 | ~spl3_109),
% 1.36/0.61    inference(avatar_split_clause,[],[f951,f944,f533,f430,f192,f114,f124,f299,f434])).
% 1.36/0.61  fof(f434,plain,(
% 1.36/0.61    spl3_52 <=> v1_relat_1(k2_funct_1(sK1))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 1.36/0.61  fof(f299,plain,(
% 1.36/0.61    spl3_29 <=> v1_funct_1(k2_funct_1(sK1))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.36/0.61  fof(f124,plain,(
% 1.36/0.61    spl3_3 <=> v2_funct_1(sK1)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.36/0.61  fof(f114,plain,(
% 1.36/0.61    spl3_1 <=> v1_funct_1(sK1)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.36/0.61  fof(f192,plain,(
% 1.36/0.61    spl3_14 <=> v1_relat_1(sK1)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.36/0.61  fof(f430,plain,(
% 1.36/0.61    spl3_51 <=> sK0 = k2_relat_1(k2_funct_1(sK1))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 1.36/0.61  fof(f533,plain,(
% 1.36/0.61    spl3_63 <=> sK1 = k5_relat_1(sK2,sK1)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 1.36/0.61  fof(f944,plain,(
% 1.36/0.61    spl3_109 <=> ! [X0] : (k2_funct_1(X0) != k2_funct_1(k5_relat_1(sK2,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(k2_funct_1(X0)) != sK0 | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_109])])).
% 1.36/0.61  fof(f951,plain,(
% 1.36/0.61    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_51 | ~spl3_63 | ~spl3_109)),
% 1.36/0.61    inference(trivial_inequality_removal,[],[f950])).
% 1.36/0.61  fof(f950,plain,(
% 1.36/0.61    sK0 != sK0 | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_51 | ~spl3_63 | ~spl3_109)),
% 1.36/0.61    inference(forward_demodulation,[],[f949,f431])).
% 1.36/0.61  fof(f431,plain,(
% 1.36/0.61    sK0 = k2_relat_1(k2_funct_1(sK1)) | ~spl3_51),
% 1.36/0.61    inference(avatar_component_clause,[],[f430])).
% 1.36/0.61  fof(f949,plain,(
% 1.36/0.61    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | sK0 != k2_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_63 | ~spl3_109)),
% 1.36/0.61    inference(trivial_inequality_removal,[],[f947])).
% 1.36/0.61  fof(f947,plain,(
% 1.36/0.61    k2_funct_1(sK1) != k2_funct_1(sK1) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | sK0 != k2_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(k2_funct_1(sK1)) | (~spl3_63 | ~spl3_109)),
% 1.36/0.61    inference(superposition,[],[f945,f535])).
% 1.36/0.61  fof(f535,plain,(
% 1.36/0.61    sK1 = k5_relat_1(sK2,sK1) | ~spl3_63),
% 1.36/0.61    inference(avatar_component_clause,[],[f533])).
% 1.36/0.61  fof(f945,plain,(
% 1.36/0.61    ( ! [X0] : (k2_funct_1(X0) != k2_funct_1(k5_relat_1(sK2,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(k2_funct_1(X0)) != sK0 | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0))) ) | ~spl3_109),
% 1.36/0.61    inference(avatar_component_clause,[],[f944])).
% 1.36/0.61  fof(f946,plain,(
% 1.36/0.61    ~spl3_16 | ~spl3_2 | ~spl3_35 | spl3_109 | ~spl3_101),
% 1.36/0.61    inference(avatar_split_clause,[],[f884,f880,f944,f334,f119,f206])).
% 1.36/0.61  fof(f206,plain,(
% 1.36/0.61    spl3_16 <=> v1_relat_1(sK2)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.36/0.61  fof(f119,plain,(
% 1.36/0.61    spl3_2 <=> v1_funct_1(sK2)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.36/0.61  fof(f334,plain,(
% 1.36/0.61    spl3_35 <=> v2_funct_1(sK2)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 1.36/0.61  fof(f880,plain,(
% 1.36/0.61    spl3_101 <=> ! [X0] : (k5_relat_1(X0,k2_funct_1(sK2)) != X0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_relat_1(X0) != sK0)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).
% 1.36/0.61  fof(f884,plain,(
% 1.36/0.61    ( ! [X0] : (k2_funct_1(X0) != k2_funct_1(k5_relat_1(sK2,X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | k2_relat_1(k2_funct_1(X0)) != sK0 | ~v2_funct_1(X0) | ~v2_funct_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl3_101),
% 1.36/0.61    inference(superposition,[],[f881,f85])).
% 1.36/0.61  fof(f85,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f37])).
% 1.36/0.61  fof(f37,plain,(
% 1.36/0.61    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.61    inference(flattening,[],[f36])).
% 1.36/0.61  fof(f36,plain,(
% 1.36/0.61    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.61    inference(ennf_transformation,[],[f11])).
% 1.36/0.61  fof(f11,axiom,(
% 1.36/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).
% 1.36/0.61  fof(f881,plain,(
% 1.36/0.61    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(sK2)) != X0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_relat_1(X0) != sK0) ) | ~spl3_101),
% 1.36/0.61    inference(avatar_component_clause,[],[f880])).
% 1.36/0.61  fof(f883,plain,(
% 1.36/0.61    sK2 != k6_relat_1(sK0) | r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.36/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.36/0.61  fof(f882,plain,(
% 1.36/0.61    ~spl3_70 | ~spl3_34 | spl3_101 | spl3_76 | ~spl3_88),
% 1.36/0.61    inference(avatar_split_clause,[],[f754,f745,f672,f880,f330,f616])).
% 1.36/0.61  fof(f616,plain,(
% 1.36/0.61    spl3_70 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 1.36/0.61  fof(f330,plain,(
% 1.36/0.61    spl3_34 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.36/0.61  fof(f672,plain,(
% 1.36/0.61    spl3_76 <=> k6_relat_1(sK0) = k2_funct_1(sK2)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 1.36/0.61  fof(f745,plain,(
% 1.36/0.61    spl3_88 <=> sK0 = k1_relat_1(k2_funct_1(sK2))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).
% 1.36/0.61  fof(f754,plain,(
% 1.36/0.61    ( ! [X0] : (k6_relat_1(sK0) = k2_funct_1(sK2) | k5_relat_1(X0,k2_funct_1(sK2)) != X0 | k2_relat_1(X0) != sK0 | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_88),
% 1.36/0.61    inference(superposition,[],[f88,f747])).
% 1.36/0.61  fof(f747,plain,(
% 1.36/0.61    sK0 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_88),
% 1.36/0.61    inference(avatar_component_clause,[],[f745])).
% 1.36/0.61  fof(f88,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f41])).
% 1.36/0.61  fof(f41,plain,(
% 1.36/0.61    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.61    inference(flattening,[],[f40])).
% 1.36/0.61  fof(f40,plain,(
% 1.36/0.61    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.61    inference(ennf_transformation,[],[f6])).
% 1.36/0.61  fof(f6,axiom,(
% 1.36/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).
% 1.36/0.61  fof(f748,plain,(
% 1.36/0.61    ~spl3_79 | spl3_88 | ~spl3_87),
% 1.36/0.61    inference(avatar_split_clause,[],[f742,f738,f745,f690])).
% 1.36/0.61  fof(f690,plain,(
% 1.36/0.61    spl3_79 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 1.36/0.61  fof(f738,plain,(
% 1.36/0.61    spl3_87 <=> sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK2))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 1.36/0.61  fof(f742,plain,(
% 1.36/0.61    sK0 = k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_87),
% 1.36/0.61    inference(superposition,[],[f740,f97])).
% 1.36/0.61  fof(f97,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.61    inference(cnf_transformation,[],[f47])).
% 1.36/0.61  fof(f47,plain,(
% 1.36/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.61    inference(ennf_transformation,[],[f13])).
% 1.36/0.61  fof(f13,axiom,(
% 1.36/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.36/0.61  fof(f740,plain,(
% 1.36/0.61    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK2)) | ~spl3_87),
% 1.36/0.61    inference(avatar_component_clause,[],[f738])).
% 1.36/0.61  fof(f741,plain,(
% 1.36/0.61    ~spl3_34 | ~spl3_68 | spl3_87 | ~spl3_79),
% 1.36/0.61    inference(avatar_split_clause,[],[f696,f690,f738,f607,f330])).
% 1.36/0.61  fof(f607,plain,(
% 1.36/0.61    spl3_68 <=> v1_funct_2(k2_funct_1(sK2),sK0,sK0)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 1.36/0.61  fof(f696,plain,(
% 1.36/0.61    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK0,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~spl3_79),
% 1.36/0.61    inference(resolution,[],[f692,f93])).
% 1.36/0.61  fof(f93,plain,(
% 1.36/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f46])).
% 1.36/0.61  fof(f46,plain,(
% 1.36/0.61    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.36/0.61    inference(flattening,[],[f45])).
% 1.36/0.61  fof(f45,plain,(
% 1.36/0.61    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.36/0.61    inference(ennf_transformation,[],[f21])).
% 1.36/0.61  fof(f21,axiom,(
% 1.36/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 1.36/0.61  fof(f692,plain,(
% 1.36/0.61    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_79),
% 1.36/0.61    inference(avatar_component_clause,[],[f690])).
% 1.36/0.61  fof(f693,plain,(
% 1.36/0.61    ~spl3_16 | ~spl3_2 | ~spl3_35 | spl3_79 | ~spl3_41 | ~spl3_75),
% 1.36/0.61    inference(avatar_split_clause,[],[f670,f659,f369,f690,f334,f119,f206])).
% 1.36/0.61  fof(f369,plain,(
% 1.36/0.61    spl3_41 <=> sK0 = k2_relat_1(sK2)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.36/0.61  fof(f659,plain,(
% 1.36/0.61    spl3_75 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 1.36/0.61  fof(f670,plain,(
% 1.36/0.61    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_41 | ~spl3_75)),
% 1.36/0.61    inference(forward_demodulation,[],[f669,f370])).
% 1.36/0.61  fof(f370,plain,(
% 1.36/0.61    sK0 = k2_relat_1(sK2) | ~spl3_41),
% 1.36/0.61    inference(avatar_component_clause,[],[f369])).
% 1.36/0.61  fof(f669,plain,(
% 1.36/0.61    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),sK0))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_75),
% 1.36/0.61    inference(superposition,[],[f661,f81])).
% 1.36/0.61  fof(f81,plain,(
% 1.36/0.61    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f33])).
% 1.36/0.61  fof(f33,plain,(
% 1.36/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.61    inference(flattening,[],[f32])).
% 1.36/0.61  fof(f32,plain,(
% 1.36/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.61    inference(ennf_transformation,[],[f9])).
% 1.36/0.61  fof(f9,axiom,(
% 1.36/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.36/0.61  fof(f661,plain,(
% 1.36/0.61    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~spl3_75),
% 1.36/0.61    inference(avatar_component_clause,[],[f659])).
% 1.36/0.61  fof(f675,plain,(
% 1.36/0.61    ~spl3_16 | ~spl3_2 | ~spl3_35 | ~spl3_34 | ~spl3_70 | ~spl3_76 | ~spl3_41 | ~spl3_47 | ~spl3_69),
% 1.36/0.61    inference(avatar_split_clause,[],[f645,f612,f406,f369,f672,f616,f330,f334,f119,f206])).
% 1.36/0.61  fof(f406,plain,(
% 1.36/0.61    spl3_47 <=> ! [X0] : (k5_relat_1(X0,sK2) != X0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_relat_1(X0) != sK0)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 1.36/0.61  fof(f612,plain,(
% 1.36/0.61    spl3_69 <=> sK0 = k2_relat_1(k2_funct_1(sK2))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 1.36/0.61  fof(f645,plain,(
% 1.36/0.61    k6_relat_1(sK0) != k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_41 | ~spl3_47 | ~spl3_69)),
% 1.36/0.61    inference(trivial_inequality_removal,[],[f644])).
% 1.36/0.61  fof(f644,plain,(
% 1.36/0.61    sK0 != sK0 | k6_relat_1(sK0) != k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_41 | ~spl3_47 | ~spl3_69)),
% 1.36/0.61    inference(forward_demodulation,[],[f643,f613])).
% 1.36/0.61  fof(f613,plain,(
% 1.36/0.61    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~spl3_69),
% 1.36/0.61    inference(avatar_component_clause,[],[f612])).
% 1.36/0.61  fof(f643,plain,(
% 1.36/0.61    k6_relat_1(sK0) != k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | sK0 != k2_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_41 | ~spl3_47)),
% 1.36/0.61    inference(forward_demodulation,[],[f413,f370])).
% 1.36/0.61  fof(f413,plain,(
% 1.36/0.61    k2_funct_1(sK2) != k6_relat_1(k2_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | sK0 != k2_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_47),
% 1.36/0.61    inference(superposition,[],[f407,f84])).
% 1.36/0.61  fof(f84,plain,(
% 1.36/0.61    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f35])).
% 1.36/0.61  fof(f35,plain,(
% 1.36/0.61    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.61    inference(flattening,[],[f34])).
% 1.36/0.61  fof(f34,plain,(
% 1.36/0.61    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.61    inference(ennf_transformation,[],[f10])).
% 1.36/0.61  fof(f10,axiom,(
% 1.36/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.36/0.61  fof(f407,plain,(
% 1.36/0.61    ( ! [X0] : (k5_relat_1(X0,sK2) != X0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_relat_1(X0) != sK0) ) | ~spl3_47),
% 1.36/0.61    inference(avatar_component_clause,[],[f406])).
% 1.36/0.61  fof(f662,plain,(
% 1.36/0.61    ~spl3_70 | ~spl3_34 | spl3_75 | ~spl3_69),
% 1.36/0.61    inference(avatar_split_clause,[],[f638,f612,f659,f330,f616])).
% 1.36/0.61  fof(f638,plain,(
% 1.36/0.61    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_69),
% 1.36/0.61    inference(superposition,[],[f78,f613])).
% 1.36/0.61  fof(f78,plain,(
% 1.36/0.61    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f29])).
% 1.36/0.61  fof(f29,plain,(
% 1.36/0.61    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.61    inference(flattening,[],[f28])).
% 1.36/0.61  fof(f28,plain,(
% 1.36/0.61    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.61    inference(ennf_transformation,[],[f20])).
% 1.36/0.61  fof(f20,axiom,(
% 1.36/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.36/0.61  fof(f630,plain,(
% 1.36/0.61    ~spl3_2 | ~spl3_16 | spl3_70),
% 1.36/0.61    inference(avatar_contradiction_clause,[],[f628])).
% 1.36/0.61  fof(f628,plain,(
% 1.36/0.61    $false | (~spl3_2 | ~spl3_16 | spl3_70)),
% 1.36/0.61    inference(unit_resulting_resolution,[],[f208,f121,f618,f79])).
% 1.36/0.61  fof(f79,plain,(
% 1.36/0.61    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f31])).
% 1.36/0.61  fof(f31,plain,(
% 1.36/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.61    inference(flattening,[],[f30])).
% 1.36/0.61  fof(f30,plain,(
% 1.36/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.61    inference(ennf_transformation,[],[f5])).
% 1.36/0.61  fof(f5,axiom,(
% 1.36/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.36/0.61  fof(f618,plain,(
% 1.36/0.61    ~v1_relat_1(k2_funct_1(sK2)) | spl3_70),
% 1.36/0.61    inference(avatar_component_clause,[],[f616])).
% 1.36/0.61  fof(f121,plain,(
% 1.36/0.61    v1_funct_1(sK2) | ~spl3_2),
% 1.36/0.61    inference(avatar_component_clause,[],[f119])).
% 1.36/0.61  fof(f208,plain,(
% 1.36/0.61    v1_relat_1(sK2) | ~spl3_16),
% 1.36/0.61    inference(avatar_component_clause,[],[f206])).
% 1.36/0.61  fof(f627,plain,(
% 1.36/0.61    ~spl3_16 | ~spl3_2 | ~spl3_35 | ~spl3_21 | spl3_69),
% 1.36/0.61    inference(avatar_split_clause,[],[f626,f612,f241,f334,f119,f206])).
% 1.36/0.61  fof(f241,plain,(
% 1.36/0.61    spl3_21 <=> sK0 = k1_relat_1(sK2)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.36/0.61  fof(f626,plain,(
% 1.36/0.61    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_21 | spl3_69)),
% 1.36/0.61    inference(trivial_inequality_removal,[],[f625])).
% 1.36/0.61  fof(f625,plain,(
% 1.36/0.61    sK0 != sK0 | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_21 | spl3_69)),
% 1.36/0.61    inference(forward_demodulation,[],[f624,f243])).
% 1.36/0.61  fof(f243,plain,(
% 1.36/0.61    sK0 = k1_relat_1(sK2) | ~spl3_21),
% 1.36/0.61    inference(avatar_component_clause,[],[f241])).
% 1.36/0.61  fof(f624,plain,(
% 1.36/0.61    sK0 != k1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_69),
% 1.36/0.61    inference(superposition,[],[f614,f82])).
% 1.36/0.61  fof(f82,plain,(
% 1.36/0.61    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f33])).
% 1.36/0.61  fof(f614,plain,(
% 1.36/0.61    sK0 != k2_relat_1(k2_funct_1(sK2)) | spl3_69),
% 1.36/0.61    inference(avatar_component_clause,[],[f612])).
% 1.36/0.61  fof(f610,plain,(
% 1.36/0.61    spl3_68 | ~spl3_41 | ~spl3_50),
% 1.36/0.61    inference(avatar_split_clause,[],[f605,f424,f369,f607])).
% 1.36/0.61  fof(f424,plain,(
% 1.36/0.61    spl3_50 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 1.36/0.61  fof(f605,plain,(
% 1.36/0.61    v1_funct_2(k2_funct_1(sK2),sK0,sK0) | (~spl3_41 | ~spl3_50)),
% 1.36/0.61    inference(forward_demodulation,[],[f426,f370])).
% 1.36/0.61  fof(f426,plain,(
% 1.36/0.61    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0) | ~spl3_50),
% 1.36/0.61    inference(avatar_component_clause,[],[f424])).
% 1.36/0.61  fof(f601,plain,(
% 1.36/0.61    spl3_35 | ~spl3_2 | ~spl3_16 | ~spl3_3 | ~spl3_38 | ~spl3_41 | ~spl3_63),
% 1.36/0.61    inference(avatar_split_clause,[],[f600,f533,f369,f354,f124,f206,f119,f334])).
% 1.36/0.61  fof(f354,plain,(
% 1.36/0.61    spl3_38 <=> ! [X1] : (k2_relat_1(X1) != sK0 | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,sK1)) | v2_funct_1(X1))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.36/0.61  fof(f600,plain,(
% 1.36/0.61    ~v2_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | v2_funct_1(sK2) | (~spl3_38 | ~spl3_41 | ~spl3_63)),
% 1.36/0.61    inference(trivial_inequality_removal,[],[f599])).
% 1.36/0.61  fof(f599,plain,(
% 1.36/0.61    sK0 != sK0 | ~v2_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | v2_funct_1(sK2) | (~spl3_38 | ~spl3_41 | ~spl3_63)),
% 1.36/0.61    inference(forward_demodulation,[],[f539,f370])).
% 1.36/0.61  fof(f539,plain,(
% 1.36/0.61    ~v2_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK0 != k2_relat_1(sK2) | v2_funct_1(sK2) | (~spl3_38 | ~spl3_63)),
% 1.36/0.61    inference(superposition,[],[f355,f535])).
% 1.36/0.61  fof(f355,plain,(
% 1.36/0.61    ( ! [X1] : (~v2_funct_1(k5_relat_1(X1,sK1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k2_relat_1(X1) != sK0 | v2_funct_1(X1)) ) | ~spl3_38),
% 1.36/0.61    inference(avatar_component_clause,[],[f354])).
% 1.36/0.61  fof(f562,plain,(
% 1.36/0.61    ~spl3_11 | ~spl3_16 | spl3_65),
% 1.36/0.61    inference(avatar_contradiction_clause,[],[f560])).
% 1.36/0.61  fof(f560,plain,(
% 1.36/0.61    $false | (~spl3_11 | ~spl3_16 | spl3_65)),
% 1.36/0.61    inference(unit_resulting_resolution,[],[f208,f180,f558,f91])).
% 1.36/0.61  fof(f91,plain,(
% 1.36/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f61])).
% 1.36/0.61  fof(f61,plain,(
% 1.36/0.61    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.36/0.61    inference(nnf_transformation,[],[f44])).
% 1.36/0.61  fof(f44,plain,(
% 1.36/0.61    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.36/0.61    inference(ennf_transformation,[],[f3])).
% 1.36/0.61  fof(f3,axiom,(
% 1.36/0.61    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.36/0.61  fof(f558,plain,(
% 1.36/0.61    ~r1_tarski(k2_relat_1(sK2),sK0) | spl3_65),
% 1.36/0.61    inference(avatar_component_clause,[],[f556])).
% 1.36/0.61  fof(f556,plain,(
% 1.36/0.61    spl3_65 <=> r1_tarski(k2_relat_1(sK2),sK0)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 1.36/0.61  fof(f180,plain,(
% 1.36/0.61    v5_relat_1(sK2,sK0) | ~spl3_11),
% 1.36/0.61    inference(avatar_component_clause,[],[f178])).
% 1.36/0.61  fof(f178,plain,(
% 1.36/0.61    spl3_11 <=> v5_relat_1(sK2,sK0)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.36/0.61  fof(f559,plain,(
% 1.36/0.61    ~spl3_65 | spl3_41 | ~spl3_64),
% 1.36/0.61    inference(avatar_split_clause,[],[f554,f550,f369,f556])).
% 1.36/0.61  fof(f550,plain,(
% 1.36/0.61    spl3_64 <=> r1_tarski(sK0,k2_relat_1(sK2))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 1.36/0.61  fof(f554,plain,(
% 1.36/0.61    sK0 = k2_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK0) | ~spl3_64),
% 1.36/0.61    inference(resolution,[],[f552,f96])).
% 1.36/0.61  fof(f96,plain,(
% 1.36/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f63])).
% 1.36/0.61  fof(f63,plain,(
% 1.36/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.61    inference(flattening,[],[f62])).
% 1.36/0.61  fof(f62,plain,(
% 1.36/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.61    inference(nnf_transformation,[],[f1])).
% 1.36/0.61  fof(f1,axiom,(
% 1.36/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.61  fof(f552,plain,(
% 1.36/0.61    r1_tarski(sK0,k2_relat_1(sK2)) | ~spl3_64),
% 1.36/0.61    inference(avatar_component_clause,[],[f550])).
% 1.36/0.61  fof(f553,plain,(
% 1.36/0.61    ~spl3_14 | ~spl3_1 | ~spl3_16 | ~spl3_2 | ~spl3_3 | spl3_64 | ~spl3_19 | ~spl3_63),
% 1.36/0.61    inference(avatar_split_clause,[],[f542,f533,f226,f550,f124,f119,f206,f114,f192])).
% 1.36/0.61  fof(f226,plain,(
% 1.36/0.61    spl3_19 <=> sK0 = k1_relat_1(sK1)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.36/0.61  fof(f542,plain,(
% 1.36/0.61    r1_tarski(sK0,k2_relat_1(sK2)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_19 | ~spl3_63)),
% 1.36/0.61    inference(forward_demodulation,[],[f541,f228])).
% 1.36/0.61  fof(f228,plain,(
% 1.36/0.61    sK0 = k1_relat_1(sK1) | ~spl3_19),
% 1.36/0.61    inference(avatar_component_clause,[],[f226])).
% 1.36/0.61  fof(f541,plain,(
% 1.36/0.61    ~v2_funct_1(sK1) | r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_63),
% 1.36/0.61    inference(trivial_inequality_removal,[],[f540])).
% 1.36/0.61  fof(f540,plain,(
% 1.36/0.61    k2_relat_1(sK1) != k2_relat_1(sK1) | ~v2_funct_1(sK1) | r1_tarski(k1_relat_1(sK1),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_63),
% 1.36/0.61    inference(superposition,[],[f89,f535])).
% 1.36/0.61  fof(f89,plain,(
% 1.36/0.61    ( ! [X0,X1] : (k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v2_funct_1(X0) | r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f43])).
% 1.36/0.61  fof(f43,plain,(
% 1.36/0.61    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.61    inference(flattening,[],[f42])).
% 1.36/0.61  fof(f42,plain,(
% 1.36/0.61    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.61    inference(ennf_transformation,[],[f8])).
% 1.36/0.61  fof(f8,axiom,(
% 1.36/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).
% 1.36/0.61  fof(f536,plain,(
% 1.36/0.61    ~spl3_2 | ~spl3_7 | ~spl3_1 | ~spl3_6 | spl3_63 | ~spl3_62),
% 1.36/0.61    inference(avatar_split_clause,[],[f523,f518,f533,f139,f114,f144,f119])).
% 1.36/0.61  fof(f144,plain,(
% 1.36/0.61    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.36/0.61  fof(f139,plain,(
% 1.36/0.61    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.36/0.61  fof(f518,plain,(
% 1.36/0.61    spl3_62 <=> sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 1.36/0.61  fof(f523,plain,(
% 1.36/0.61    sK1 = k5_relat_1(sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~spl3_62),
% 1.36/0.61    inference(superposition,[],[f520,f105])).
% 1.36/0.61  fof(f105,plain,(
% 1.36/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f55])).
% 1.36/0.61  fof(f55,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.36/0.61    inference(flattening,[],[f54])).
% 1.36/0.61  fof(f54,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.36/0.61    inference(ennf_transformation,[],[f17])).
% 1.36/0.61  fof(f17,axiom,(
% 1.36/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.36/0.61  fof(f520,plain,(
% 1.36/0.61    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~spl3_62),
% 1.36/0.61    inference(avatar_component_clause,[],[f518])).
% 1.36/0.61  fof(f521,plain,(
% 1.36/0.61    ~spl3_2 | ~spl3_7 | ~spl3_1 | ~spl3_6 | spl3_62 | ~spl3_6 | ~spl3_15),
% 1.36/0.61    inference(avatar_split_clause,[],[f461,f197,f139,f518,f139,f114,f144,f119])).
% 1.36/0.61  fof(f197,plain,(
% 1.36/0.61    spl3_15 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.36/0.61  fof(f461,plain,(
% 1.36/0.61    sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | (~spl3_6 | ~spl3_15)),
% 1.36/0.61    inference(resolution,[],[f246,f199])).
% 1.36/0.61  fof(f199,plain,(
% 1.36/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) | ~spl3_15),
% 1.36/0.61    inference(avatar_component_clause,[],[f197])).
% 1.36/0.61  fof(f246,plain,(
% 1.36/0.61    ( ! [X4,X2,X3,X1] : (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,X1,X2,sK0,X3,X4),sK1) | sK1 = k1_partfun1(sK0,X1,X2,sK0,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X3)) ) | ~spl3_6),
% 1.36/0.61    inference(resolution,[],[f154,f107])).
% 1.36/0.61  fof(f107,plain,(
% 1.36/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f57])).
% 1.36/0.61  fof(f57,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.36/0.61    inference(flattening,[],[f56])).
% 1.36/0.61  fof(f56,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.36/0.61    inference(ennf_transformation,[],[f16])).
% 1.36/0.61  fof(f16,axiom,(
% 1.36/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.36/0.61  fof(f154,plain,(
% 1.36/0.61    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK1 = X0 | ~r2_relset_1(sK0,sK0,X0,sK1)) ) | ~spl3_6),
% 1.36/0.61    inference(resolution,[],[f141,f103])).
% 1.36/0.61  fof(f103,plain,(
% 1.36/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.61    inference(cnf_transformation,[],[f64])).
% 1.36/0.61  fof(f64,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.61    inference(nnf_transformation,[],[f53])).
% 1.36/0.61  fof(f53,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.61    inference(flattening,[],[f52])).
% 1.36/0.61  fof(f52,plain,(
% 1.36/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.36/0.61    inference(ennf_transformation,[],[f15])).
% 1.36/0.61  fof(f15,axiom,(
% 1.36/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.36/0.61  fof(f141,plain,(
% 1.36/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_6),
% 1.36/0.61    inference(avatar_component_clause,[],[f139])).
% 1.36/0.61  fof(f448,plain,(
% 1.36/0.61    ~spl3_1 | ~spl3_14 | spl3_52),
% 1.36/0.61    inference(avatar_contradiction_clause,[],[f446])).
% 1.36/0.61  fof(f446,plain,(
% 1.36/0.61    $false | (~spl3_1 | ~spl3_14 | spl3_52)),
% 1.36/0.61    inference(unit_resulting_resolution,[],[f194,f116,f436,f79])).
% 1.36/0.61  fof(f436,plain,(
% 1.36/0.61    ~v1_relat_1(k2_funct_1(sK1)) | spl3_52),
% 1.36/0.61    inference(avatar_component_clause,[],[f434])).
% 1.36/0.61  fof(f116,plain,(
% 1.36/0.61    v1_funct_1(sK1) | ~spl3_1),
% 1.36/0.61    inference(avatar_component_clause,[],[f114])).
% 1.36/0.61  fof(f194,plain,(
% 1.36/0.61    v1_relat_1(sK1) | ~spl3_14),
% 1.36/0.61    inference(avatar_component_clause,[],[f192])).
% 1.36/0.61  fof(f445,plain,(
% 1.36/0.61    ~spl3_14 | ~spl3_1 | ~spl3_3 | ~spl3_19 | spl3_51),
% 1.36/0.61    inference(avatar_split_clause,[],[f444,f430,f226,f124,f114,f192])).
% 1.36/0.61  fof(f444,plain,(
% 1.36/0.61    ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_19 | spl3_51)),
% 1.36/0.61    inference(trivial_inequality_removal,[],[f443])).
% 1.36/0.61  fof(f443,plain,(
% 1.36/0.61    sK0 != sK0 | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_19 | spl3_51)),
% 1.36/0.61    inference(forward_demodulation,[],[f442,f228])).
% 1.36/0.61  fof(f442,plain,(
% 1.36/0.61    sK0 != k1_relat_1(sK1) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl3_51),
% 1.36/0.61    inference(superposition,[],[f432,f82])).
% 1.36/0.61  fof(f432,plain,(
% 1.36/0.61    sK0 != k2_relat_1(k2_funct_1(sK1)) | spl3_51),
% 1.36/0.61    inference(avatar_component_clause,[],[f430])).
% 1.36/0.61  fof(f427,plain,(
% 1.36/0.61    ~spl3_2 | ~spl3_24 | spl3_50 | ~spl3_35 | ~spl3_32 | ~spl3_43),
% 1.36/0.61    inference(avatar_split_clause,[],[f422,f383,f314,f334,f424,f264,f119])).
% 1.36/0.61  fof(f264,plain,(
% 1.36/0.61    spl3_24 <=> v1_funct_2(sK2,sK0,k2_relat_1(sK2))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.36/0.61  fof(f314,plain,(
% 1.36/0.61    spl3_32 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.36/0.61  fof(f383,plain,(
% 1.36/0.61    spl3_43 <=> k2_relat_1(sK2) = k2_relset_1(sK0,k2_relat_1(sK2),sK2)),
% 1.36/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 1.36/0.61  fof(f422,plain,(
% 1.36/0.61    ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0) | ~v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_32 | ~spl3_43)),
% 1.36/0.61    inference(trivial_inequality_removal,[],[f421])).
% 1.36/0.61  fof(f421,plain,(
% 1.36/0.61    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0) | ~v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_32 | ~spl3_43)),
% 1.36/0.61    inference(forward_demodulation,[],[f321,f384])).
% 1.36/0.61  fof(f384,plain,(
% 1.36/0.61    k2_relat_1(sK2) = k2_relset_1(sK0,k2_relat_1(sK2),sK2) | ~spl3_43),
% 1.36/0.61    inference(avatar_component_clause,[],[f383])).
% 1.36/0.61  fof(f321,plain,(
% 1.36/0.61    k2_relat_1(sK2) != k2_relset_1(sK0,k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),sK0) | ~v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_32),
% 1.36/0.61    inference(resolution,[],[f316,f101])).
% 1.36/0.61  fof(f101,plain,(
% 1.36/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.36/0.61    inference(cnf_transformation,[],[f51])).
% 1.36/0.61  fof(f51,plain,(
% 1.36/0.61    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.36/0.61    inference(flattening,[],[f50])).
% 1.36/0.61  fof(f50,plain,(
% 1.36/0.61    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.36/0.61    inference(ennf_transformation,[],[f19])).
% 1.36/0.61  fof(f19,axiom,(
% 1.36/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.36/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.36/0.61  fof(f316,plain,(
% 1.36/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | ~spl3_32),
% 1.36/0.61    inference(avatar_component_clause,[],[f314])).
% 1.36/0.63  fof(f412,plain,(
% 1.36/0.63    ~spl3_16 | ~spl3_2 | spl3_47 | spl3_48 | ~spl3_21),
% 1.36/0.63    inference(avatar_split_clause,[],[f249,f241,f409,f406,f119,f206])).
% 1.36/0.63  fof(f409,plain,(
% 1.36/0.63    spl3_48 <=> sK2 = k6_relat_1(sK0)),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 1.36/0.63  fof(f249,plain,(
% 1.36/0.63    ( ! [X0] : (sK2 = k6_relat_1(sK0) | k5_relat_1(X0,sK2) != X0 | k2_relat_1(X0) != sK0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_21),
% 1.36/0.63    inference(superposition,[],[f88,f243])).
% 1.36/0.63  fof(f390,plain,(
% 1.36/0.63    ~spl3_32 | spl3_43),
% 1.36/0.63    inference(avatar_contradiction_clause,[],[f387])).
% 1.36/0.63  fof(f387,plain,(
% 1.36/0.63    $false | (~spl3_32 | spl3_43)),
% 1.36/0.63    inference(unit_resulting_resolution,[],[f316,f385,f98])).
% 1.36/0.63  fof(f98,plain,(
% 1.36/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.63    inference(cnf_transformation,[],[f48])).
% 1.36/0.63  fof(f48,plain,(
% 1.36/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.63    inference(ennf_transformation,[],[f14])).
% 1.36/0.63  fof(f14,axiom,(
% 1.36/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.36/0.63  fof(f385,plain,(
% 1.36/0.63    k2_relat_1(sK2) != k2_relset_1(sK0,k2_relat_1(sK2),sK2) | spl3_43),
% 1.36/0.63    inference(avatar_component_clause,[],[f383])).
% 1.36/0.63  fof(f381,plain,(
% 1.36/0.63    ~spl3_25 | spl3_42),
% 1.36/0.63    inference(avatar_contradiction_clause,[],[f378])).
% 1.36/0.63  fof(f378,plain,(
% 1.36/0.63    $false | (~spl3_25 | spl3_42)),
% 1.36/0.63    inference(unit_resulting_resolution,[],[f271,f376,f98])).
% 1.36/0.63  fof(f376,plain,(
% 1.36/0.63    k2_relat_1(sK1) != k2_relset_1(sK0,k2_relat_1(sK1),sK1) | spl3_42),
% 1.36/0.63    inference(avatar_component_clause,[],[f374])).
% 1.36/0.63  fof(f374,plain,(
% 1.36/0.63    spl3_42 <=> k2_relat_1(sK1) = k2_relset_1(sK0,k2_relat_1(sK1),sK1)),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.36/0.63  fof(f271,plain,(
% 1.36/0.63    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | ~spl3_25),
% 1.36/0.63    inference(avatar_component_clause,[],[f269])).
% 1.36/0.63  fof(f269,plain,(
% 1.36/0.63    spl3_25 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.36/0.63  fof(f377,plain,(
% 1.36/0.63    ~spl3_1 | ~spl3_20 | spl3_29 | ~spl3_3 | ~spl3_42 | ~spl3_25),
% 1.36/0.63    inference(avatar_split_clause,[],[f279,f269,f374,f124,f299,f236,f114])).
% 1.36/0.63  fof(f236,plain,(
% 1.36/0.63    spl3_20 <=> v1_funct_2(sK1,sK0,k2_relat_1(sK1))),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.36/0.63  fof(f279,plain,(
% 1.36/0.63    k2_relat_1(sK1) != k2_relset_1(sK0,k2_relat_1(sK1),sK1) | ~v2_funct_1(sK1) | v1_funct_1(k2_funct_1(sK1)) | ~v1_funct_2(sK1,sK0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~spl3_25),
% 1.36/0.63    inference(resolution,[],[f271,f100])).
% 1.36/0.63  fof(f100,plain,(
% 1.36/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_1(k2_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f51])).
% 1.36/0.63  fof(f372,plain,(
% 1.36/0.63    ~spl3_7 | ~spl3_41 | spl3_36),
% 1.36/0.63    inference(avatar_split_clause,[],[f367,f338,f369,f144])).
% 1.36/0.63  fof(f338,plain,(
% 1.36/0.63    spl3_36 <=> sK0 = k2_relset_1(sK0,sK0,sK2)),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.36/0.63  fof(f367,plain,(
% 1.36/0.63    sK0 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_36),
% 1.36/0.63    inference(superposition,[],[f340,f98])).
% 1.36/0.63  fof(f340,plain,(
% 1.36/0.63    sK0 != k2_relset_1(sK0,sK0,sK2) | spl3_36),
% 1.36/0.63    inference(avatar_component_clause,[],[f338])).
% 1.36/0.63  fof(f356,plain,(
% 1.36/0.63    ~spl3_14 | ~spl3_1 | spl3_38 | ~spl3_19),
% 1.36/0.63    inference(avatar_split_clause,[],[f231,f226,f354,f114,f192])).
% 1.36/0.63  fof(f231,plain,(
% 1.36/0.63    ( ! [X1] : (k2_relat_1(X1) != sK0 | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,sK1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl3_19),
% 1.36/0.63    inference(superposition,[],[f86,f228])).
% 1.36/0.63  fof(f86,plain,(
% 1.36/0.63    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f39])).
% 1.36/0.63  fof(f39,plain,(
% 1.36/0.63    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.63    inference(flattening,[],[f38])).
% 1.36/0.63  fof(f38,plain,(
% 1.36/0.63    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.36/0.63    inference(ennf_transformation,[],[f7])).
% 1.36/0.63  fof(f7,axiom,(
% 1.36/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.36/0.63  fof(f341,plain,(
% 1.36/0.63    ~spl3_2 | ~spl3_5 | spl3_34 | ~spl3_35 | ~spl3_36 | ~spl3_7),
% 1.36/0.63    inference(avatar_split_clause,[],[f173,f144,f338,f334,f330,f134,f119])).
% 1.36/0.63  fof(f134,plain,(
% 1.36/0.63    spl3_5 <=> v1_funct_2(sK2,sK0,sK0)),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.36/0.63  fof(f173,plain,(
% 1.36/0.63    sK0 != k2_relset_1(sK0,sK0,sK2) | ~v2_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~spl3_7),
% 1.36/0.63    inference(resolution,[],[f146,f100])).
% 1.36/0.63  fof(f146,plain,(
% 1.36/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_7),
% 1.36/0.63    inference(avatar_component_clause,[],[f144])).
% 1.36/0.63  fof(f317,plain,(
% 1.36/0.63    ~spl3_16 | ~spl3_2 | spl3_32 | ~spl3_21),
% 1.36/0.63    inference(avatar_split_clause,[],[f253,f241,f314,f119,f206])).
% 1.36/0.63  fof(f253,plain,(
% 1.36/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_21),
% 1.36/0.63    inference(superposition,[],[f78,f243])).
% 1.36/0.63  fof(f272,plain,(
% 1.36/0.63    ~spl3_14 | ~spl3_1 | spl3_25 | ~spl3_19),
% 1.36/0.63    inference(avatar_split_clause,[],[f234,f226,f269,f114,f192])).
% 1.36/0.63  fof(f234,plain,(
% 1.36/0.63    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_19),
% 1.36/0.63    inference(superposition,[],[f78,f228])).
% 1.36/0.63  fof(f267,plain,(
% 1.36/0.63    ~spl3_16 | ~spl3_2 | spl3_24 | ~spl3_21),
% 1.36/0.63    inference(avatar_split_clause,[],[f252,f241,f264,f119,f206])).
% 1.36/0.63  fof(f252,plain,(
% 1.36/0.63    v1_funct_2(sK2,sK0,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_21),
% 1.36/0.63    inference(superposition,[],[f77,f243])).
% 1.36/0.63  fof(f77,plain,(
% 1.36/0.63    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f29])).
% 1.36/0.63  fof(f244,plain,(
% 1.36/0.63    ~spl3_7 | spl3_21 | ~spl3_18),
% 1.36/0.63    inference(avatar_split_clause,[],[f223,f219,f241,f144])).
% 1.36/0.63  fof(f219,plain,(
% 1.36/0.63    spl3_18 <=> sK0 = k1_relset_1(sK0,sK0,sK2)),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.36/0.63  fof(f223,plain,(
% 1.36/0.63    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_18),
% 1.36/0.63    inference(superposition,[],[f221,f97])).
% 1.36/0.63  fof(f221,plain,(
% 1.36/0.63    sK0 = k1_relset_1(sK0,sK0,sK2) | ~spl3_18),
% 1.36/0.63    inference(avatar_component_clause,[],[f219])).
% 1.36/0.63  fof(f239,plain,(
% 1.36/0.63    ~spl3_14 | ~spl3_1 | spl3_20 | ~spl3_19),
% 1.36/0.63    inference(avatar_split_clause,[],[f233,f226,f236,f114,f192])).
% 1.36/0.63  fof(f233,plain,(
% 1.36/0.63    v1_funct_2(sK1,sK0,k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_19),
% 1.36/0.63    inference(superposition,[],[f77,f228])).
% 1.36/0.63  fof(f229,plain,(
% 1.36/0.63    ~spl3_6 | spl3_19 | ~spl3_17),
% 1.36/0.63    inference(avatar_split_clause,[],[f216,f212,f226,f139])).
% 1.36/0.63  fof(f212,plain,(
% 1.36/0.63    spl3_17 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.36/0.63  fof(f216,plain,(
% 1.36/0.63    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_17),
% 1.36/0.63    inference(superposition,[],[f214,f97])).
% 1.36/0.63  fof(f214,plain,(
% 1.36/0.63    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_17),
% 1.36/0.63    inference(avatar_component_clause,[],[f212])).
% 1.36/0.63  fof(f222,plain,(
% 1.36/0.63    ~spl3_2 | ~spl3_5 | spl3_18 | ~spl3_7),
% 1.36/0.63    inference(avatar_split_clause,[],[f170,f144,f219,f134,f119])).
% 1.36/0.63  fof(f170,plain,(
% 1.36/0.63    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~spl3_7),
% 1.36/0.63    inference(resolution,[],[f146,f93])).
% 1.36/0.63  fof(f215,plain,(
% 1.36/0.63    ~spl3_1 | ~spl3_4 | spl3_17 | ~spl3_6),
% 1.36/0.63    inference(avatar_split_clause,[],[f153,f139,f212,f129,f114])).
% 1.36/0.63  fof(f129,plain,(
% 1.36/0.63    spl3_4 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.36/0.63  fof(f153,plain,(
% 1.36/0.63    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_6),
% 1.36/0.63    inference(resolution,[],[f141,f93])).
% 1.36/0.63  fof(f209,plain,(
% 1.36/0.63    ~spl3_13 | spl3_16 | ~spl3_7),
% 1.36/0.63    inference(avatar_split_clause,[],[f176,f144,f206,f188])).
% 1.36/0.63  fof(f188,plain,(
% 1.36/0.63    spl3_13 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.36/0.63  fof(f176,plain,(
% 1.36/0.63    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | ~spl3_7),
% 1.36/0.63    inference(resolution,[],[f146,f75])).
% 1.36/0.63  fof(f75,plain,(
% 1.36/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f27])).
% 1.36/0.63  fof(f27,plain,(
% 1.36/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.36/0.63    inference(ennf_transformation,[],[f2])).
% 1.36/0.63  fof(f2,axiom,(
% 1.36/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.36/0.63  fof(f204,plain,(
% 1.36/0.63    spl3_13),
% 1.36/0.63    inference(avatar_contradiction_clause,[],[f201])).
% 1.36/0.63  fof(f201,plain,(
% 1.36/0.63    $false | spl3_13),
% 1.36/0.63    inference(unit_resulting_resolution,[],[f90,f190])).
% 1.36/0.63  fof(f190,plain,(
% 1.36/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl3_13),
% 1.36/0.63    inference(avatar_component_clause,[],[f188])).
% 1.36/0.63  fof(f90,plain,(
% 1.36/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.36/0.63    inference(cnf_transformation,[],[f4])).
% 1.36/0.63  fof(f4,axiom,(
% 1.36/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.36/0.63  fof(f200,plain,(
% 1.36/0.63    spl3_15),
% 1.36/0.63    inference(avatar_split_clause,[],[f71,f197])).
% 1.36/0.63  fof(f71,plain,(
% 1.36/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 1.36/0.63    inference(cnf_transformation,[],[f60])).
% 1.36/0.63  fof(f60,plain,(
% 1.36/0.63    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.36/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f59,f58])).
% 1.36/0.63  fof(f58,plain,(
% 1.36/0.63    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.36/0.63    introduced(choice_axiom,[])).
% 1.36/0.63  fof(f59,plain,(
% 1.36/0.63    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.36/0.63    introduced(choice_axiom,[])).
% 1.36/0.63  fof(f26,plain,(
% 1.36/0.63    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.36/0.63    inference(flattening,[],[f25])).
% 1.36/0.63  fof(f25,plain,(
% 1.36/0.63    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.36/0.63    inference(ennf_transformation,[],[f23])).
% 1.36/0.63  fof(f23,negated_conjecture,(
% 1.36/0.63    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.36/0.63    inference(negated_conjecture,[],[f22])).
% 1.36/0.63  fof(f22,conjecture,(
% 1.36/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).
% 1.36/0.63  fof(f195,plain,(
% 1.36/0.63    ~spl3_13 | spl3_14 | ~spl3_6),
% 1.36/0.63    inference(avatar_split_clause,[],[f159,f139,f192,f188])).
% 1.36/0.63  fof(f159,plain,(
% 1.36/0.63    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | ~spl3_6),
% 1.36/0.63    inference(resolution,[],[f141,f75])).
% 1.36/0.63  fof(f186,plain,(
% 1.36/0.63    spl3_12 | ~spl3_7),
% 1.36/0.63    inference(avatar_split_clause,[],[f172,f144,f183])).
% 1.36/0.63  fof(f183,plain,(
% 1.36/0.63    spl3_12 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.36/0.63  fof(f172,plain,(
% 1.36/0.63    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_7),
% 1.36/0.63    inference(resolution,[],[f146,f112])).
% 1.36/0.63  fof(f112,plain,(
% 1.36/0.63    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.36/0.63    inference(duplicate_literal_removal,[],[f111])).
% 1.36/0.63  fof(f111,plain,(
% 1.36/0.63    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.63    inference(equality_resolution,[],[f104])).
% 1.36/0.63  fof(f104,plain,(
% 1.36/0.63    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.36/0.63    inference(cnf_transformation,[],[f64])).
% 1.36/0.63  fof(f181,plain,(
% 1.36/0.63    spl3_11 | ~spl3_7),
% 1.36/0.63    inference(avatar_split_clause,[],[f175,f144,f178])).
% 1.36/0.63  fof(f175,plain,(
% 1.36/0.63    v5_relat_1(sK2,sK0) | ~spl3_7),
% 1.36/0.63    inference(resolution,[],[f146,f99])).
% 1.36/0.63  fof(f99,plain,(
% 1.36/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f49])).
% 1.36/0.63  fof(f49,plain,(
% 1.36/0.63    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.36/0.63    inference(ennf_transformation,[],[f24])).
% 1.36/0.63  fof(f24,plain,(
% 1.36/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.36/0.63    inference(pure_predicate_removal,[],[f12])).
% 1.36/0.63  fof(f12,axiom,(
% 1.36/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.36/0.63  fof(f152,plain,(
% 1.36/0.63    ~spl3_8),
% 1.36/0.63    inference(avatar_split_clause,[],[f108,f149])).
% 1.36/0.63  fof(f149,plain,(
% 1.36/0.63    spl3_8 <=> r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))),
% 1.36/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.36/0.63  fof(f108,plain,(
% 1.36/0.63    ~r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0))),
% 1.36/0.63    inference(definition_unfolding,[],[f73,f74])).
% 1.36/0.63  fof(f74,plain,(
% 1.36/0.63    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.36/0.63    inference(cnf_transformation,[],[f18])).
% 1.36/0.63  fof(f18,axiom,(
% 1.36/0.63    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.36/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.36/0.63  fof(f73,plain,(
% 1.36/0.63    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 1.36/0.63    inference(cnf_transformation,[],[f60])).
% 1.36/0.63  fof(f147,plain,(
% 1.36/0.63    spl3_7),
% 1.36/0.63    inference(avatar_split_clause,[],[f70,f144])).
% 1.36/0.63  fof(f70,plain,(
% 1.36/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.36/0.63    inference(cnf_transformation,[],[f60])).
% 1.36/0.63  fof(f142,plain,(
% 1.36/0.63    spl3_6),
% 1.36/0.63    inference(avatar_split_clause,[],[f67,f139])).
% 1.36/0.63  fof(f67,plain,(
% 1.36/0.63    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.36/0.63    inference(cnf_transformation,[],[f60])).
% 1.36/0.63  fof(f137,plain,(
% 1.36/0.63    spl3_5),
% 1.36/0.63    inference(avatar_split_clause,[],[f69,f134])).
% 1.36/0.63  fof(f69,plain,(
% 1.36/0.63    v1_funct_2(sK2,sK0,sK0)),
% 1.36/0.63    inference(cnf_transformation,[],[f60])).
% 1.36/0.63  fof(f132,plain,(
% 1.36/0.63    spl3_4),
% 1.36/0.63    inference(avatar_split_clause,[],[f66,f129])).
% 1.36/0.63  fof(f66,plain,(
% 1.36/0.63    v1_funct_2(sK1,sK0,sK0)),
% 1.36/0.63    inference(cnf_transformation,[],[f60])).
% 1.36/0.63  fof(f127,plain,(
% 1.36/0.63    spl3_3),
% 1.36/0.63    inference(avatar_split_clause,[],[f72,f124])).
% 1.36/0.63  fof(f72,plain,(
% 1.36/0.63    v2_funct_1(sK1)),
% 1.36/0.63    inference(cnf_transformation,[],[f60])).
% 1.36/0.63  fof(f122,plain,(
% 1.36/0.63    spl3_2),
% 1.36/0.63    inference(avatar_split_clause,[],[f68,f119])).
% 1.36/0.63  fof(f68,plain,(
% 1.36/0.63    v1_funct_1(sK2)),
% 1.36/0.63    inference(cnf_transformation,[],[f60])).
% 1.36/0.63  fof(f117,plain,(
% 1.36/0.63    spl3_1),
% 1.36/0.63    inference(avatar_split_clause,[],[f65,f114])).
% 1.36/0.63  fof(f65,plain,(
% 1.36/0.63    v1_funct_1(sK1)),
% 1.36/0.63    inference(cnf_transformation,[],[f60])).
% 1.36/0.63  % SZS output end Proof for theBenchmark
% 1.36/0.63  % (29206)------------------------------
% 1.36/0.63  % (29206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.63  % (29206)Termination reason: Refutation
% 1.36/0.63  
% 1.36/0.63  % (29206)Memory used [KB]: 11641
% 1.36/0.63  % (29206)Time elapsed: 0.179 s
% 1.36/0.63  % (29206)------------------------------
% 1.36/0.63  % (29206)------------------------------
% 1.36/0.64  % (29195)Success in time 0.27 s
%------------------------------------------------------------------------------
