%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 169 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  254 ( 638 expanded)
%              Number of equality atoms :   55 ( 178 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f48,f56,f61,f62,f66,f73,f87,f100,f115,f121,f136,f157,f158])).

% (29341)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (29335)Refutation not found, incomplete strategy% (29335)------------------------------
% (29335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29335)Termination reason: Refutation not found, incomplete strategy

% (29335)Memory used [KB]: 10618
% (29335)Time elapsed: 0.073 s
% (29335)------------------------------
% (29335)------------------------------
fof(f158,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK0
    | v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f157,plain,
    ( spl3_17
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f153,f131,f64,f155])).

fof(f155,plain,
    ( spl3_17
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f64,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f131,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f153,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(resolution,[],[f135,f82])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f80,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(resolution,[],[f77,f65])).

fof(f65,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(resolution,[],[f74,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f74,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_7 ),
    inference(resolution,[],[f35,f65])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f135,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f136,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f134,f50,f46,f131])).

fof(f46,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f123,f37])).

fof(f37,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f123,plain,
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

fof(f121,plain,
    ( spl3_2
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f118,f112,f64,f43])).

fof(f43,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f112,plain,
    ( spl3_12
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(resolution,[],[f113,f74])).

fof(f113,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f115,plain,
    ( spl3_12
    | ~ spl3_4
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f110,f58,f54,f39,f50,f112])).

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

fof(f110,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1)
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(resolution,[],[f109,f55])).

fof(f55,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | v1_xboole_0(X0) )
    | spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f108,f40])).

fof(f40,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f30,f59])).

fof(f59,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f100,plain,
    ( spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f90,f85,f98])).

fof(f98,plain,
    ( spl3_11
  <=> v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f85,plain,
    ( spl3_9
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f90,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(superposition,[],[f27,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f27,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f87,plain,
    ( spl3_9
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f83,f70,f64,f85])).

fof(f70,plain,
    ( spl3_8
  <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f83,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f82,f71])).

fof(f71,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f73,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f68,f70])).

fof(f68,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (29340)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.45  % (29347)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (29339)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (29335)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (29339)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f41,f48,f56,f61,f62,f66,f73,f87,f100,f115,f121,f136,f157,f158])).
% 0.20/0.47  % (29341)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (29335)Refutation not found, incomplete strategy% (29335)------------------------------
% 0.20/0.47  % (29335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (29335)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (29335)Memory used [KB]: 10618
% 0.20/0.47  % (29335)Time elapsed: 0.073 s
% 0.20/0.47  % (29335)------------------------------
% 0.20/0.47  % (29335)------------------------------
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    k1_xboole_0 != sK2 | k1_xboole_0 != sK0 | v1_partfun1(sK2,sK0) | ~v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    spl3_17 | ~spl3_7 | ~spl3_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f153,f131,f64,f155])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    spl3_17 <=> k1_xboole_0 = sK2),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl3_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    k1_xboole_0 = sK2 | (~spl3_7 | ~spl3_14)),
% 0.20/0.47    inference(resolution,[],[f135,f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.20/0.47    inference(forward_demodulation,[],[f80,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.20/0.47    inference(resolution,[],[f77,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.20/0.47    inference(resolution,[],[f74,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_7),
% 0.20/0.47    inference(resolution,[],[f35,f65])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f131])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    spl3_14 | ~spl3_3 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f134,f50,f46,f131])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl3_3 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_4)),
% 0.20/0.47    inference(forward_demodulation,[],[f123,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl3_3 | ~spl3_4)),
% 0.20/0.47    inference(superposition,[],[f51,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f46])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f50])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    spl3_2 | ~spl3_7 | ~spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f118,f112,f64,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl3_2 <=> k1_xboole_0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    spl3_12 <=> v1_xboole_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | (~spl3_7 | ~spl3_12)),
% 0.20/0.47    inference(resolution,[],[f113,f74])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    v1_xboole_0(sK1) | ~spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f112])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    spl3_12 | ~spl3_4 | spl3_1 | ~spl3_5 | ~spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f110,f58,f54,f39,f50,f112])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl3_1 <=> v1_partfun1(sK2,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    spl3_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl3_6 <=> v1_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1) | (spl3_1 | ~spl3_5 | ~spl3_6)),
% 0.20/0.47    inference(resolution,[],[f109,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    v1_funct_2(sK2,sK0,sK1) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f54])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_funct_2(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_xboole_0(X0)) ) | (spl3_1 | ~spl3_6)),
% 0.20/0.47    inference(resolution,[],[f108,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ~v1_partfun1(sK2,sK0) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f39])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl3_6),
% 0.20/0.47    inference(resolution,[],[f30,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    v1_funct_1(sK2) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f58])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl3_11 | ~spl3_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f90,f85,f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl3_11 <=> v1_partfun1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    spl3_9 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    v1_partfun1(k1_xboole_0,k1_xboole_0) | ~spl3_9),
% 0.20/0.47    inference(superposition,[],[f27,f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl3_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f85])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl3_9 | ~spl3_7 | ~spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f83,f70,f64,f85])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl3_8 <=> m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    k1_xboole_0 = k6_partfun1(k1_xboole_0) | (~spl3_7 | ~spl3_8)),
% 0.20/0.47    inference(resolution,[],[f82,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f70])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f68,f70])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.47    inference(superposition,[],[f28,f37])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f26,f64])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f58])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (((~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f20,f50])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f22,f54])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ~spl3_2 | spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f24,f46,f43])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f25,f39])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ~v1_partfun1(sK2,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (29339)------------------------------
% 0.20/0.47  % (29339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (29339)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (29339)Memory used [KB]: 10618
% 0.20/0.47  % (29339)Time elapsed: 0.044 s
% 0.20/0.47  % (29339)------------------------------
% 0.20/0.47  % (29339)------------------------------
% 0.20/0.47  % (29343)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (29332)Success in time 0.127 s
%------------------------------------------------------------------------------
