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
% DateTime   : Thu Dec  3 13:06:41 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 159 expanded)
%              Number of leaves         :   22 (  61 expanded)
%              Depth                    :    8
%              Number of atoms          :  245 ( 602 expanded)
%              Number of equality atoms :   54 ( 175 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f48,f56,f61,f62,f66,f74,f85,f98,f107,f111,f126,f146,f147])).

fof(f147,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK0
    | v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f146,plain,
    ( spl3_17
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f142,f121,f64,f144])).

fof(f144,plain,
    ( spl3_17
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f64,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f121,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f142,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(resolution,[],[f125,f80])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f78,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f78,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(resolution,[],[f75,f65])).

fof(f65,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f32,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f125,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f126,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f124,f50,f46,f121])).

fof(f46,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f124,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f113,f37])).

fof(f37,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f113,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f51,f47])).

fof(f47,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f51,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f111,plain,
    ( spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f109,f104,f43])).

fof(f43,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f104,plain,
    ( spl3_12
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_12 ),
    inference(resolution,[],[f105,f29])).

fof(f105,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f107,plain,
    ( spl3_12
    | ~ spl3_4
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f102,f58,f54,f39,f50,f104])).

fof(f39,plain,
    ( spl3_1
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f58,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f102,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1)
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(resolution,[],[f101,f55])).

fof(f55,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | v1_xboole_0(X0) )
    | spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f100,f40])).

fof(f40,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f31,f59])).

fof(f59,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f98,plain,
    ( spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f88,f83,f96])).

fof(f96,plain,
    ( spl3_11
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f83,plain,
    ( spl3_9
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f88,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(superposition,[],[f27,f84])).

fof(f84,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f27,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f85,plain,
    ( spl3_9
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f81,f71,f64,f83])).

fof(f71,plain,
    ( spl3_8
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f81,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f80,f72])).

fof(f72,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f74,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f69,f71])).

fof(f69,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f28,f37])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f66,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f62,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f58])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ v1_partfun1(sK2,sK0)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ v1_partfun1(X2,X0)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ v1_partfun1(sK2,sK0)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) )
         => ( v1_partfun1(X2,X0)
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f61,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f24,f46,f43])).

fof(f24,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f39])).

fof(f25,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (1335)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.13/0.42  % (1335)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f148,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(avatar_sat_refutation,[],[f41,f48,f56,f61,f62,f66,f74,f85,f98,f107,f111,f126,f146,f147])).
% 0.13/0.42  fof(f147,plain,(
% 0.13/0.42    k1_xboole_0 != sK2 | k1_xboole_0 != sK0 | v1_partfun1(sK2,sK0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.13/0.42    introduced(theory_tautology_sat_conflict,[])).
% 0.13/0.42  fof(f146,plain,(
% 0.13/0.42    spl3_17 | ~spl3_7 | ~spl3_14),
% 0.13/0.42    inference(avatar_split_clause,[],[f142,f121,f64,f144])).
% 0.13/0.42  fof(f144,plain,(
% 0.13/0.42    spl3_17 <=> k1_xboole_0 = sK2),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.13/0.42  fof(f64,plain,(
% 0.13/0.42    spl3_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.13/0.42  fof(f121,plain,(
% 0.13/0.42    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.13/0.42  fof(f142,plain,(
% 0.13/0.42    k1_xboole_0 = sK2 | (~spl3_7 | ~spl3_14)),
% 0.13/0.42    inference(resolution,[],[f125,f80])).
% 0.13/0.42  fof(f80,plain,(
% 0.13/0.42    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.13/0.42    inference(forward_demodulation,[],[f78,f36])).
% 0.13/0.42  fof(f36,plain,(
% 0.13/0.42    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.13/0.42    inference(equality_resolution,[],[f35])).
% 0.13/0.42  fof(f35,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.13/0.42    inference(cnf_transformation,[],[f18])).
% 0.13/0.42  fof(f18,plain,(
% 0.13/0.42    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.13/0.42    inference(flattening,[],[f17])).
% 0.13/0.42  fof(f17,plain,(
% 0.13/0.42    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.13/0.42    inference(nnf_transformation,[],[f3])).
% 0.13/0.42  fof(f3,axiom,(
% 0.13/0.42    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.13/0.42  fof(f78,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.13/0.42    inference(resolution,[],[f75,f65])).
% 0.13/0.42  fof(f65,plain,(
% 0.13/0.42    v1_xboole_0(k1_xboole_0) | ~spl3_7),
% 0.13/0.42    inference(avatar_component_clause,[],[f64])).
% 0.13/0.42  fof(f75,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X0) )),
% 0.13/0.42    inference(resolution,[],[f32,f29])).
% 0.13/0.42  fof(f29,plain,(
% 0.13/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.13/0.42    inference(cnf_transformation,[],[f11])).
% 0.13/0.42  fof(f11,plain,(
% 0.13/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.13/0.42    inference(ennf_transformation,[],[f2])).
% 0.13/0.42  fof(f2,axiom,(
% 0.13/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.13/0.42  fof(f32,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f14])).
% 0.13/0.42  fof(f14,plain,(
% 0.13/0.42    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.13/0.42    inference(ennf_transformation,[],[f4])).
% 0.13/0.42  fof(f4,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.13/0.42  fof(f125,plain,(
% 0.13/0.42    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_14),
% 0.13/0.42    inference(avatar_component_clause,[],[f121])).
% 0.13/0.42  fof(f126,plain,(
% 0.13/0.42    spl3_14 | ~spl3_3 | ~spl3_4),
% 0.13/0.42    inference(avatar_split_clause,[],[f124,f50,f46,f121])).
% 0.13/0.42  fof(f46,plain,(
% 0.13/0.42    spl3_3 <=> k1_xboole_0 = sK0),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.13/0.42  fof(f50,plain,(
% 0.13/0.42    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.13/0.42  fof(f124,plain,(
% 0.13/0.42    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_4)),
% 0.13/0.42    inference(forward_demodulation,[],[f113,f37])).
% 0.13/0.42  fof(f37,plain,(
% 0.13/0.42    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.13/0.42    inference(equality_resolution,[],[f34])).
% 0.13/0.42  fof(f34,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.13/0.42    inference(cnf_transformation,[],[f18])).
% 0.13/0.42  fof(f113,plain,(
% 0.13/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl3_3 | ~spl3_4)),
% 0.13/0.42    inference(superposition,[],[f51,f47])).
% 0.13/0.42  fof(f47,plain,(
% 0.13/0.42    k1_xboole_0 = sK0 | ~spl3_3),
% 0.13/0.42    inference(avatar_component_clause,[],[f46])).
% 0.13/0.42  fof(f51,plain,(
% 0.13/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.13/0.42    inference(avatar_component_clause,[],[f50])).
% 0.13/0.42  fof(f111,plain,(
% 0.13/0.42    spl3_2 | ~spl3_12),
% 0.13/0.42    inference(avatar_split_clause,[],[f109,f104,f43])).
% 0.13/0.42  fof(f43,plain,(
% 0.13/0.42    spl3_2 <=> k1_xboole_0 = sK1),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.13/0.42  fof(f104,plain,(
% 0.13/0.42    spl3_12 <=> v1_xboole_0(sK1)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.13/0.42  fof(f109,plain,(
% 0.13/0.42    k1_xboole_0 = sK1 | ~spl3_12),
% 0.13/0.42    inference(resolution,[],[f105,f29])).
% 0.13/0.42  fof(f105,plain,(
% 0.13/0.42    v1_xboole_0(sK1) | ~spl3_12),
% 0.13/0.42    inference(avatar_component_clause,[],[f104])).
% 0.13/0.42  fof(f107,plain,(
% 0.13/0.42    spl3_12 | ~spl3_4 | spl3_1 | ~spl3_5 | ~spl3_6),
% 0.13/0.42    inference(avatar_split_clause,[],[f102,f58,f54,f39,f50,f104])).
% 0.13/0.42  fof(f39,plain,(
% 0.13/0.42    spl3_1 <=> v1_partfun1(sK2,sK0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.13/0.42  fof(f54,plain,(
% 0.13/0.42    spl3_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.13/0.42  fof(f58,plain,(
% 0.13/0.42    spl3_6 <=> v1_funct_1(sK2)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.13/0.42  fof(f102,plain,(
% 0.13/0.42    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1) | (spl3_1 | ~spl3_5 | ~spl3_6)),
% 0.13/0.42    inference(resolution,[],[f101,f55])).
% 0.13/0.42  fof(f55,plain,(
% 0.13/0.42    v1_funct_2(sK2,sK0,sK1) | ~spl3_5),
% 0.13/0.42    inference(avatar_component_clause,[],[f54])).
% 0.13/0.42  fof(f101,plain,(
% 0.13/0.42    ( ! [X0] : (~v1_funct_2(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_xboole_0(X0)) ) | (spl3_1 | ~spl3_6)),
% 0.13/0.42    inference(resolution,[],[f100,f40])).
% 0.13/0.42  fof(f40,plain,(
% 0.13/0.42    ~v1_partfun1(sK2,sK0) | spl3_1),
% 0.13/0.42    inference(avatar_component_clause,[],[f39])).
% 0.13/0.42  fof(f100,plain,(
% 0.13/0.42    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl3_6),
% 0.13/0.42    inference(resolution,[],[f31,f59])).
% 0.13/0.42  fof(f59,plain,(
% 0.13/0.42    v1_funct_1(sK2) | ~spl3_6),
% 0.13/0.42    inference(avatar_component_clause,[],[f58])).
% 0.13/0.42  fof(f31,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f13])).
% 0.13/0.42  fof(f13,plain,(
% 0.13/0.42    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.13/0.42    inference(flattening,[],[f12])).
% 0.13/0.42  fof(f12,plain,(
% 0.13/0.42    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,axiom,(
% 0.13/0.42    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.13/0.42  fof(f98,plain,(
% 0.13/0.42    spl3_11 | ~spl3_9),
% 0.13/0.42    inference(avatar_split_clause,[],[f88,f83,f96])).
% 0.13/0.42  fof(f96,plain,(
% 0.13/0.42    spl3_11 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.13/0.42  fof(f83,plain,(
% 0.13/0.42    spl3_9 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.13/0.42  fof(f88,plain,(
% 0.13/0.42    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl3_9),
% 0.13/0.42    inference(superposition,[],[f27,f84])).
% 0.13/0.42  fof(f84,plain,(
% 0.13/0.42    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl3_9),
% 0.13/0.42    inference(avatar_component_clause,[],[f83])).
% 0.13/0.42  fof(f27,plain,(
% 0.13/0.42    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f6])).
% 0.13/0.42  fof(f6,axiom,(
% 0.13/0.42    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.13/0.42  fof(f85,plain,(
% 0.13/0.42    spl3_9 | ~spl3_7 | ~spl3_8),
% 0.13/0.42    inference(avatar_split_clause,[],[f81,f71,f64,f83])).
% 0.13/0.42  fof(f71,plain,(
% 0.13/0.42    spl3_8 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.13/0.42  fof(f81,plain,(
% 0.13/0.42    k1_xboole_0 = k6_partfun1(k1_xboole_0) | (~spl3_7 | ~spl3_8)),
% 0.13/0.42    inference(resolution,[],[f80,f72])).
% 0.13/0.42  fof(f72,plain,(
% 0.13/0.42    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_8),
% 0.13/0.42    inference(avatar_component_clause,[],[f71])).
% 0.13/0.42  fof(f74,plain,(
% 0.13/0.42    spl3_8),
% 0.13/0.42    inference(avatar_split_clause,[],[f69,f71])).
% 0.13/0.42  fof(f69,plain,(
% 0.13/0.42    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.13/0.42    inference(superposition,[],[f28,f37])).
% 0.13/0.42  fof(f28,plain,(
% 0.13/0.42    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f6])).
% 0.13/0.42  fof(f66,plain,(
% 0.13/0.42    spl3_7),
% 0.13/0.42    inference(avatar_split_clause,[],[f26,f64])).
% 0.13/0.42  fof(f26,plain,(
% 0.13/0.42    v1_xboole_0(k1_xboole_0)),
% 0.13/0.42    inference(cnf_transformation,[],[f1])).
% 0.13/0.42  fof(f1,axiom,(
% 0.13/0.42    v1_xboole_0(k1_xboole_0)),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.13/0.42  fof(f62,plain,(
% 0.13/0.42    spl3_6),
% 0.13/0.42    inference(avatar_split_clause,[],[f19,f58])).
% 0.13/0.42  fof(f19,plain,(
% 0.13/0.42    v1_funct_1(sK2)),
% 0.13/0.42    inference(cnf_transformation,[],[f16])).
% 0.13/0.42  fof(f16,plain,(
% 0.13/0.42    ~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.13/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).
% 0.13/0.42  fof(f15,plain,(
% 0.13/0.42    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.13/0.42    introduced(choice_axiom,[])).
% 0.13/0.42  fof(f10,plain,(
% 0.13/0.42    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.13/0.42    inference(flattening,[],[f9])).
% 0.13/0.42  fof(f9,plain,(
% 0.13/0.42    ? [X0,X1,X2] : (((~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.13/0.42    inference(ennf_transformation,[],[f8])).
% 0.13/0.42  fof(f8,negated_conjecture,(
% 0.13/0.42    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.13/0.42    inference(negated_conjecture,[],[f7])).
% 0.13/0.42  fof(f7,conjecture,(
% 0.13/0.42    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.13/0.42  fof(f61,plain,(
% 0.13/0.42    spl3_4),
% 0.13/0.42    inference(avatar_split_clause,[],[f20,f50])).
% 0.13/0.42  fof(f20,plain,(
% 0.13/0.42    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.13/0.42    inference(cnf_transformation,[],[f16])).
% 0.13/0.42  fof(f56,plain,(
% 0.13/0.42    spl3_5),
% 0.13/0.42    inference(avatar_split_clause,[],[f22,f54])).
% 0.13/0.42  fof(f22,plain,(
% 0.13/0.42    v1_funct_2(sK2,sK0,sK1)),
% 0.13/0.42    inference(cnf_transformation,[],[f16])).
% 0.13/0.42  fof(f48,plain,(
% 0.13/0.42    ~spl3_2 | spl3_3),
% 0.13/0.42    inference(avatar_split_clause,[],[f24,f46,f43])).
% 0.13/0.42  fof(f24,plain,(
% 0.13/0.42    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.13/0.42    inference(cnf_transformation,[],[f16])).
% 0.13/0.42  fof(f41,plain,(
% 0.13/0.42    ~spl3_1),
% 0.13/0.42    inference(avatar_split_clause,[],[f25,f39])).
% 0.13/0.42  fof(f25,plain,(
% 0.13/0.42    ~v1_partfun1(sK2,sK0)),
% 0.13/0.42    inference(cnf_transformation,[],[f16])).
% 0.13/0.42  % SZS output end Proof for theBenchmark
% 0.13/0.42  % (1335)------------------------------
% 0.13/0.42  % (1335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.42  % (1335)Termination reason: Refutation
% 0.13/0.42  
% 0.13/0.42  % (1335)Memory used [KB]: 10618
% 0.13/0.42  % (1335)Time elapsed: 0.009 s
% 0.13/0.42  % (1335)------------------------------
% 0.13/0.42  % (1335)------------------------------
% 0.13/0.42  % (1328)Success in time 0.066 s
%------------------------------------------------------------------------------
