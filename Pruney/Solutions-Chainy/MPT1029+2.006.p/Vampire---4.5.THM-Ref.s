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
% DateTime   : Thu Dec  3 13:06:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 183 expanded)
%              Number of leaves         :   24 (  80 expanded)
%              Depth                    :    7
%              Number of atoms          :  270 ( 641 expanded)
%              Number of equality atoms :   47 ( 137 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f484,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f51,f61,f67,f68,f73,f81,f98,f130,f137,f296,f325,f380,f430,f451,f476,f483])).

fof(f483,plain,
    ( spl3_41
    | ~ spl3_43 ),
    inference(avatar_contradiction_clause,[],[f482])).

fof(f482,plain,
    ( $false
    | spl3_41
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f480,f450])).

fof(f450,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl3_41 ),
    inference(avatar_component_clause,[],[f448])).

fof(f448,plain,
    ( spl3_41
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f480,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_43 ),
    inference(superposition,[],[f27,f474])).

fof(f474,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl3_43
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f27,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f476,plain,
    ( spl3_43
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f467,f106,f70,f472])).

fof(f70,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f106,plain,
    ( spl3_11
  <=> v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f467,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f72,f108,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f108,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f72,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f451,plain,
    ( ~ spl3_41
    | spl3_36
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f439,f426,f322,f448])).

fof(f322,plain,
    ( spl3_36
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f426,plain,
    ( spl3_39
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f439,plain,
    ( ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | spl3_36
    | ~ spl3_39 ),
    inference(backward_demodulation,[],[f324,f428])).

fof(f428,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f426])).

fof(f324,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl3_36 ),
    inference(avatar_component_clause,[],[f322])).

fof(f430,plain,
    ( spl3_39
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f421,f125,f70,f426])).

fof(f125,plain,
    ( spl3_15
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f421,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f72,f127,f35])).

fof(f127,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f125])).

fof(f380,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f326,f53,f48,f134])).

fof(f134,plain,
    ( spl3_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f48,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f53,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f326,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f298,f37])).

fof(f37,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
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

fof(f298,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f55,f50])).

fof(f50,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f325,plain,
    ( ~ spl3_36
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f297,f48,f39,f322])).

fof(f39,plain,
    ( spl3_1
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f297,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f41,f50])).

fof(f41,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f296,plain,
    ( spl3_10
    | spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f272,f63,f58,f53,f39,f93])).

fof(f93,plain,
    ( spl3_10
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f58,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f63,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f272,plain,
    ( v1_xboole_0(sK1)
    | spl3_1
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f65,f41,f60,f55,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
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

fof(f60,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f65,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f137,plain,
    ( ~ spl3_16
    | ~ spl3_7
    | spl3_15 ),
    inference(avatar_split_clause,[],[f131,f125,f70,f134])).

fof(f131,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_7
    | spl3_15 ),
    inference(unit_resulting_resolution,[],[f72,f126,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f126,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f125])).

fof(f130,plain,
    ( spl3_11
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f129,f77,f70,f106])).

fof(f77,plain,
    ( spl3_8
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f129,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f104,f72])).

fof(f104,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_8 ),
    inference(resolution,[],[f29,f79])).

fof(f79,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f98,plain,
    ( ~ spl3_10
    | spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f83,f70,f44,f93])).

fof(f44,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f83,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_2
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f72,f46,f35])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f81,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f75,f77])).

fof(f75,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f28,f37])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f73,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f68,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f63])).

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

fof(f67,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f53])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f58])).

fof(f22,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f24,f48,f44])).

fof(f24,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f39])).

fof(f25,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (10277)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (10285)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (10288)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (10279)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (10280)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (10287)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (10287)Refutation not found, incomplete strategy% (10287)------------------------------
% 0.21/0.51  % (10287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10287)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10287)Memory used [KB]: 6140
% 0.21/0.51  % (10287)Time elapsed: 0.074 s
% 0.21/0.51  % (10287)------------------------------
% 0.21/0.51  % (10287)------------------------------
% 0.21/0.51  % (10285)Refutation not found, incomplete strategy% (10285)------------------------------
% 0.21/0.51  % (10285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10285)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10285)Memory used [KB]: 1663
% 0.21/0.51  % (10285)Time elapsed: 0.081 s
% 0.21/0.51  % (10285)------------------------------
% 0.21/0.51  % (10285)------------------------------
% 0.21/0.52  % (10288)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f484,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f42,f51,f61,f67,f68,f73,f81,f98,f130,f137,f296,f325,f380,f430,f451,f476,f483])).
% 0.21/0.52  fof(f483,plain,(
% 0.21/0.52    spl3_41 | ~spl3_43),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f482])).
% 0.21/0.52  fof(f482,plain,(
% 0.21/0.52    $false | (spl3_41 | ~spl3_43)),
% 0.21/0.52    inference(subsumption_resolution,[],[f480,f450])).
% 0.21/0.52  fof(f450,plain,(
% 0.21/0.52    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | spl3_41),
% 0.21/0.52    inference(avatar_component_clause,[],[f448])).
% 0.21/0.52  fof(f448,plain,(
% 0.21/0.52    spl3_41 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.52  fof(f480,plain,(
% 0.21/0.52    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl3_43),
% 0.21/0.52    inference(superposition,[],[f27,f474])).
% 0.21/0.52  fof(f474,plain,(
% 0.21/0.52    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl3_43),
% 0.21/0.52    inference(avatar_component_clause,[],[f472])).
% 0.21/0.52  fof(f472,plain,(
% 0.21/0.52    spl3_43 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.21/0.52  fof(f476,plain,(
% 0.21/0.52    spl3_43 | ~spl3_7 | ~spl3_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f467,f106,f70,f472])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl3_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl3_11 <=> v1_xboole_0(k6_partfun1(k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f467,plain,(
% 0.21/0.52    k1_xboole_0 = k6_partfun1(k1_xboole_0) | (~spl3_7 | ~spl3_11)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f72,f108,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0) | ~spl3_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f451,plain,(
% 0.21/0.52    ~spl3_41 | spl3_36 | ~spl3_39),
% 0.21/0.52    inference(avatar_split_clause,[],[f439,f426,f322,f448])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    spl3_36 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.52  fof(f426,plain,(
% 0.21/0.52    spl3_39 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.52  fof(f439,plain,(
% 0.21/0.52    ~v1_partfun1(k1_xboole_0,k1_xboole_0) | (spl3_36 | ~spl3_39)),
% 0.21/0.52    inference(backward_demodulation,[],[f324,f428])).
% 0.21/0.52  fof(f428,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl3_39),
% 0.21/0.52    inference(avatar_component_clause,[],[f426])).
% 0.21/0.52  fof(f324,plain,(
% 0.21/0.52    ~v1_partfun1(sK2,k1_xboole_0) | spl3_36),
% 0.21/0.52    inference(avatar_component_clause,[],[f322])).
% 0.21/0.52  fof(f430,plain,(
% 0.21/0.52    spl3_39 | ~spl3_7 | ~spl3_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f421,f125,f70,f426])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    spl3_15 <=> v1_xboole_0(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.52  fof(f421,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | (~spl3_7 | ~spl3_15)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f72,f127,f35])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    v1_xboole_0(sK2) | ~spl3_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f125])).
% 0.21/0.52  fof(f380,plain,(
% 0.21/0.52    spl3_16 | ~spl3_3 | ~spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f326,f53,f48,f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl3_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl3_3 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f326,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_4)),
% 0.21/0.52    inference(forward_demodulation,[],[f298,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f298,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl3_3 | ~spl3_4)),
% 0.21/0.52    inference(backward_demodulation,[],[f55,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f48])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f53])).
% 0.21/0.52  fof(f325,plain,(
% 0.21/0.52    ~spl3_36 | spl3_1 | ~spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f297,f48,f39,f322])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    spl3_1 <=> v1_partfun1(sK2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    ~v1_partfun1(sK2,k1_xboole_0) | (spl3_1 | ~spl3_3)),
% 0.21/0.52    inference(backward_demodulation,[],[f41,f50])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ~v1_partfun1(sK2,sK0) | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f39])).
% 0.21/0.52  fof(f296,plain,(
% 0.21/0.52    spl3_10 | spl3_1 | ~spl3_4 | ~spl3_5 | ~spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f272,f63,f58,f53,f39,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    spl3_10 <=> v1_xboole_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    spl3_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl3_6 <=> v1_funct_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | (spl3_1 | ~spl3_4 | ~spl3_5 | ~spl3_6)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f65,f41,f60,f55,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    v1_funct_2(sK2,sK0,sK1) | ~spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f58])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    v1_funct_1(sK2) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ~spl3_16 | ~spl3_7 | spl3_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f131,f125,f70,f134])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_7 | spl3_15)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f72,f126,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ~v1_xboole_0(sK2) | spl3_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f125])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    spl3_11 | ~spl3_7 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f129,f77,f70,f106])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl3_8 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    v1_xboole_0(k6_partfun1(k1_xboole_0)) | (~spl3_7 | ~spl3_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f104,f72])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0) | ~spl3_8),
% 0.21/0.52    inference(resolution,[],[f29,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ~spl3_10 | spl3_2 | ~spl3_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f83,f70,f44,f93])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1) | (spl3_2 | ~spl3_7)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f72,f46,f35])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f44])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f75,f77])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.52    inference(superposition,[],[f28,f37])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl3_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f26,f70])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f19,f63])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (((~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f20,f53])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f22,f58])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ~spl3_2 | spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f24,f48,f44])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f39])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ~v1_partfun1(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (10288)------------------------------
% 0.21/0.52  % (10288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10288)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (10288)Memory used [KB]: 10874
% 0.21/0.52  % (10288)Time elapsed: 0.083 s
% 0.21/0.52  % (10288)------------------------------
% 0.21/0.52  % (10288)------------------------------
% 0.21/0.52  % (10271)Success in time 0.158 s
%------------------------------------------------------------------------------
