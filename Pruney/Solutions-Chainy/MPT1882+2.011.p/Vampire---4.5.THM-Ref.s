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
% DateTime   : Thu Dec  3 13:22:01 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 421 expanded)
%              Number of leaves         :   22 ( 119 expanded)
%              Depth                    :   23
%              Number of atoms          :  555 (3086 expanded)
%              Number of equality atoms :   44 ( 120 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f87,f185,f203,f212,f328])).

fof(f328,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f326,f141])).

fof(f141,plain,
    ( v2_tex_2(sK3,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_3
  <=> v2_tex_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f326,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f325,f102])).

fof(f102,plain,
    ( ~ sP0(sK3,sK2)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f100,f81])).

fof(f81,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_1
  <=> v3_tex_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f100,plain,
    ( ~ sP0(sK3,sK2)
    | v3_tex_2(sK3,sK2) ),
    inference(resolution,[],[f99,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

% (28448)Refutation not found, incomplete strategy% (28448)------------------------------
% (28448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28448)Termination reason: Refutation not found, incomplete strategy

% (28448)Memory used [KB]: 1791
% (28448)Time elapsed: 0.207 s
% (28448)------------------------------
% (28448)------------------------------
fof(f28,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f99,plain,(
    sP1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f98,f47])).

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ v1_zfmisc_1(sK3)
      | ~ v3_tex_2(sK3,sK2) )
    & ( v1_zfmisc_1(sK3)
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK2) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

% (28461)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f33,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK2) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK3)
        | ~ v3_tex_2(sK3,sK2) )
      & ( v1_zfmisc_1(sK3)
        | v3_tex_2(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

fof(f98,plain,
    ( sP1(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f65,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f325,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f307,f94])).

fof(f94,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f69,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f75,f54])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f307,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sP0(sK3,sK2)
    | ~ v2_tex_2(sK3,sK2)
    | spl5_1
    | ~ spl5_3 ),
    inference(superposition,[],[f116,f299])).

fof(f299,plain,
    ( k1_xboole_0 = sK4(sK3,sK2)
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f298,f48])).

fof(f48,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f298,plain,
    ( v1_xboole_0(sK3)
    | k1_xboole_0 = sK4(sK3,sK2)
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f297,f47])).

fof(f297,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_xboole_0(sK3)
    | k1_xboole_0 = sK4(sK3,sK2)
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f296,f46])).

fof(f46,plain,(
    v2_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f296,plain,
    ( ~ v2_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(sK3)
    | k1_xboole_0 = sK4(sK3,sK2)
    | spl5_1
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f295,f102])).

fof(f295,plain,
    ( sP0(sK3,sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(sK3)
    | k1_xboole_0 = sK4(sK3,sK2)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f294,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f294,plain,
    ( v2_struct_0(sK2)
    | sP0(sK3,sK2)
    | ~ v2_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2)
    | v1_xboole_0(sK3)
    | k1_xboole_0 = sK4(sK3,sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f289,f141])).

fof(f289,plain,(
    ! [X6,X5] :
      ( ~ v2_tex_2(X6,X5)
      | v2_struct_0(X5)
      | sP0(X6,X5)
      | ~ v2_tdlat_3(X5)
      | ~ l1_pre_topc(X5)
      | v1_xboole_0(X6)
      | k1_xboole_0 = sK4(X6,X5) ) ),
    inference(resolution,[],[f194,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f74,f52])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f194,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(sK4(X1,X0))
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v1_xboole_0(sK4(X1,X0))
      | v1_xboole_0(X1)
      | sP0(X1,X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(resolution,[],[f170,f125])).

fof(f125,plain,(
    ! [X2,X3] :
      ( ~ v1_zfmisc_1(sK4(X2,X3))
      | v1_xboole_0(sK4(X2,X3))
      | v1_xboole_0(X2)
      | sP0(X2,X3)
      | ~ v2_tex_2(X2,X3) ) ),
    inference(subsumption_resolution,[],[f119,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK4(X0,X1))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK4(X0,X1) != X0
          & r1_tarski(X0,sK4(X0,X1))
          & v2_tex_2(sK4(X0,X1),X1)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK4(X0,X1) != X0
        & r1_tarski(X0,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ v2_tex_2(X0,X1) )
      & ( ( ! [X3] :
              ( X0 = X3
              | ~ r1_tarski(X0,X3)
              | ~ v2_tex_2(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & v2_tex_2(X0,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ v2_tex_2(X1,X0) )
      & ( ( ! [X2] :
              ( X1 = X2
              | ~ r1_tarski(X1,X2)
              | ~ v2_tex_2(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v2_tex_2(X1,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f119,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,sK4(X2,X3))
      | ~ v1_zfmisc_1(sK4(X2,X3))
      | v1_xboole_0(sK4(X2,X3))
      | v1_xboole_0(X2)
      | sP0(X2,X3)
      | ~ v2_tex_2(X2,X3) ) ),
    inference(extensionality_resolution,[],[f55,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X0
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f170,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(sK4(X0,X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_tdlat_3(X1)
      | v2_struct_0(X1)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f169,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK4(X0,X1),X1)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(sK4(X0,X1),X1)
      | v1_zfmisc_1(sK4(X0,X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_tdlat_3(X1)
      | v2_struct_0(X1)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(resolution,[],[f154,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_zfmisc_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f153,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f153,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f67,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(X0,X1),X0)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f112,f63])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK4(X0,X1))
      | ~ r1_tarski(sK4(X0,X1),X0)
      | sP0(X0,X1)
      | ~ v2_tex_2(X0,X1) ) ),
    inference(extensionality_resolution,[],[f73,f64])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f212,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f211,f83,f140])).

fof(f83,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f211,plain,
    ( ~ v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f210,f44])).

fof(f210,plain,
    ( ~ v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f209,f46])).

fof(f209,plain,
    ( ~ v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f208,f47])).

fof(f208,plain,
    ( ~ v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f172,f48])).

fof(f172,plain,
    ( ~ v1_zfmisc_1(sK3)
    | v2_tex_2(sK3,sK2)
    | v1_xboole_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f171,f49])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f68,f56])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f203,plain,
    ( spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f195,f201])).

fof(f201,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f200,f44])).

fof(f200,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v2_struct_0(sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f199,f46])).

fof(f199,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f198,f47])).

fof(f198,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f168,f85])).

fof(f85,plain,
    ( ~ v1_zfmisc_1(sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f168,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v1_zfmisc_1(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_tdlat_3(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f154,f49])).

fof(f195,plain,
    ( v2_tex_2(sK3,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f184,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f184,plain,
    ( sP0(sK3,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl5_5
  <=> sP0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f185,plain,
    ( spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f101,f79,f182])).

fof(f101,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | sP0(sK3,sK2) ),
    inference(resolution,[],[f99,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ v3_tex_2(X1,X0)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f50,f83,f79])).

fof(f50,plain,
    ( v1_zfmisc_1(sK3)
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f51,f83,f79])).

fof(f51,plain,
    ( ~ v1_zfmisc_1(sK3)
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:28:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.38/0.56  % (28449)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.38/0.56  % (28447)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.56  % (28455)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.59/0.57  % (28474)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.59/0.59  % (28464)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.59/0.59  % (28474)Refutation not found, incomplete strategy% (28474)------------------------------
% 1.59/0.59  % (28474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (28458)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.59/0.60  % (28451)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.59/0.60  % (28450)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.59/0.60  % (28451)Refutation not found, incomplete strategy% (28451)------------------------------
% 1.59/0.60  % (28451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.60  % (28451)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.60  
% 1.59/0.60  % (28451)Memory used [KB]: 1791
% 1.59/0.60  % (28451)Time elapsed: 0.170 s
% 1.59/0.60  % (28451)------------------------------
% 1.59/0.60  % (28451)------------------------------
% 1.59/0.61  % (28452)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.59/0.61  % (28458)Refutation not found, incomplete strategy% (28458)------------------------------
% 1.59/0.61  % (28458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (28458)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.61  
% 1.59/0.61  % (28458)Memory used [KB]: 10746
% 1.59/0.61  % (28458)Time elapsed: 0.154 s
% 1.59/0.61  % (28458)------------------------------
% 1.59/0.61  % (28458)------------------------------
% 1.59/0.61  % (28474)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.61  
% 1.59/0.61  % (28474)Memory used [KB]: 6396
% 1.59/0.61  % (28474)Time elapsed: 0.157 s
% 1.59/0.61  % (28474)------------------------------
% 1.59/0.61  % (28474)------------------------------
% 1.59/0.61  % (28464)Refutation not found, incomplete strategy% (28464)------------------------------
% 1.59/0.61  % (28464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (28464)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.61  
% 1.59/0.61  % (28464)Memory used [KB]: 10746
% 1.59/0.61  % (28464)Time elapsed: 0.173 s
% 1.59/0.61  % (28464)------------------------------
% 1.59/0.61  % (28464)------------------------------
% 1.59/0.61  % (28453)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.62  % (28463)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.59/0.62  % (28471)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.59/0.63  % (28462)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.59/0.63  % (28477)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.59/0.63  % (28473)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.59/0.63  % (28460)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.59/0.63  % (28475)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.59/0.63  % (28472)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.59/0.63  % (28454)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.59/0.64  % (28468)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.59/0.64  % (28448)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.59/0.64  % (28467)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.59/0.64  % (28453)Refutation found. Thanks to Tanya!
% 1.59/0.64  % SZS status Theorem for theBenchmark
% 1.59/0.64  % SZS output start Proof for theBenchmark
% 1.59/0.64  fof(f350,plain,(
% 1.59/0.64    $false),
% 1.59/0.64    inference(avatar_sat_refutation,[],[f86,f87,f185,f203,f212,f328])).
% 1.59/0.64  fof(f328,plain,(
% 1.59/0.64    spl5_1 | ~spl5_3),
% 1.59/0.64    inference(avatar_contradiction_clause,[],[f327])).
% 1.59/0.64  fof(f327,plain,(
% 1.59/0.64    $false | (spl5_1 | ~spl5_3)),
% 1.59/0.64    inference(subsumption_resolution,[],[f326,f141])).
% 1.59/0.64  fof(f141,plain,(
% 1.59/0.64    v2_tex_2(sK3,sK2) | ~spl5_3),
% 1.59/0.64    inference(avatar_component_clause,[],[f140])).
% 1.59/0.64  fof(f140,plain,(
% 1.59/0.64    spl5_3 <=> v2_tex_2(sK3,sK2)),
% 1.59/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.59/0.64  fof(f326,plain,(
% 1.59/0.64    ~v2_tex_2(sK3,sK2) | (spl5_1 | ~spl5_3)),
% 1.59/0.64    inference(subsumption_resolution,[],[f325,f102])).
% 1.59/0.64  fof(f102,plain,(
% 1.59/0.64    ~sP0(sK3,sK2) | spl5_1),
% 1.59/0.64    inference(subsumption_resolution,[],[f100,f81])).
% 1.59/0.64  fof(f81,plain,(
% 1.59/0.64    ~v3_tex_2(sK3,sK2) | spl5_1),
% 1.59/0.64    inference(avatar_component_clause,[],[f79])).
% 1.59/0.64  fof(f79,plain,(
% 1.59/0.64    spl5_1 <=> v3_tex_2(sK3,sK2)),
% 1.59/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.59/0.64  fof(f100,plain,(
% 1.59/0.64    ~sP0(sK3,sK2) | v3_tex_2(sK3,sK2)),
% 1.59/0.64    inference(resolution,[],[f99,f58])).
% 1.59/0.64  fof(f58,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v3_tex_2(X1,X0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f35])).
% 1.59/0.64  fof(f35,plain,(
% 1.59/0.64    ! [X0,X1] : (((v3_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v3_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 1.59/0.64    inference(nnf_transformation,[],[f28])).
% 1.59/0.64  % (28448)Refutation not found, incomplete strategy% (28448)------------------------------
% 1.59/0.64  % (28448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.64  % (28448)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.64  
% 1.59/0.64  % (28448)Memory used [KB]: 1791
% 1.59/0.64  % (28448)Time elapsed: 0.207 s
% 1.59/0.64  % (28448)------------------------------
% 1.59/0.64  % (28448)------------------------------
% 1.59/0.64  fof(f28,plain,(
% 1.59/0.64    ! [X0,X1] : ((v3_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 1.59/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.59/0.64  fof(f99,plain,(
% 1.59/0.64    sP1(sK2,sK3)),
% 1.59/0.64    inference(subsumption_resolution,[],[f98,f47])).
% 1.59/0.64  fof(f47,plain,(
% 1.59/0.64    l1_pre_topc(sK2)),
% 1.59/0.64    inference(cnf_transformation,[],[f34])).
% 1.59/0.64  fof(f34,plain,(
% 1.59/0.64    ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.59/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f33,f32])).
% 1.59/0.64  fof(f32,plain,(
% 1.59/0.64    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.59/0.64    introduced(choice_axiom,[])).
% 1.59/0.64  % (28461)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.59/0.64  fof(f33,plain,(
% 1.59/0.64    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK2)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)) & (v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & ~v1_xboole_0(sK3))),
% 1.59/0.64    introduced(choice_axiom,[])).
% 1.59/0.64  fof(f31,plain,(
% 1.59/0.64    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.59/0.64    inference(flattening,[],[f30])).
% 1.59/0.64  fof(f30,plain,(
% 1.59/0.64    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.59/0.64    inference(nnf_transformation,[],[f16])).
% 1.59/0.64  fof(f16,plain,(
% 1.59/0.64    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.59/0.64    inference(flattening,[],[f15])).
% 1.59/0.64  fof(f15,plain,(
% 1.59/0.64    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.59/0.64    inference(ennf_transformation,[],[f14])).
% 1.59/0.64  fof(f14,negated_conjecture,(
% 1.59/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.59/0.64    inference(negated_conjecture,[],[f13])).
% 1.59/0.64  fof(f13,conjecture,(
% 1.59/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 1.59/0.64  fof(f98,plain,(
% 1.59/0.64    sP1(sK2,sK3) | ~l1_pre_topc(sK2)),
% 1.59/0.64    inference(resolution,[],[f65,f49])).
% 1.59/0.64  fof(f49,plain,(
% 1.59/0.64    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.59/0.64    inference(cnf_transformation,[],[f34])).
% 1.59/0.64  fof(f65,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f29])).
% 1.59/0.64  fof(f29,plain,(
% 1.59/0.64    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/0.64    inference(definition_folding,[],[f22,f28,f27])).
% 1.59/0.64  fof(f27,plain,(
% 1.59/0.64    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)))),
% 1.59/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.59/0.64  fof(f22,plain,(
% 1.59/0.64    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/0.64    inference(flattening,[],[f21])).
% 1.59/0.64  fof(f21,plain,(
% 1.59/0.64    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.59/0.64    inference(ennf_transformation,[],[f10])).
% 1.59/0.64  fof(f10,axiom,(
% 1.59/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 1.59/0.64  fof(f325,plain,(
% 1.59/0.64    sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | (spl5_1 | ~spl5_3)),
% 1.59/0.64    inference(subsumption_resolution,[],[f307,f94])).
% 1.59/0.64  fof(f94,plain,(
% 1.59/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.59/0.64    inference(superposition,[],[f69,f93])).
% 1.59/0.64  fof(f93,plain,(
% 1.59/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.59/0.64    inference(forward_demodulation,[],[f75,f54])).
% 1.59/0.64  fof(f54,plain,(
% 1.59/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.59/0.64    inference(cnf_transformation,[],[f5])).
% 1.59/0.64  fof(f5,axiom,(
% 1.59/0.64    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.59/0.64  fof(f75,plain,(
% 1.59/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.59/0.64    inference(definition_unfolding,[],[f53,f70])).
% 1.59/0.64  fof(f70,plain,(
% 1.59/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f6])).
% 1.59/0.64  fof(f6,axiom,(
% 1.59/0.64    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.59/0.64  fof(f53,plain,(
% 1.59/0.64    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f3])).
% 1.59/0.64  fof(f3,axiom,(
% 1.59/0.64    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.59/0.64  fof(f69,plain,(
% 1.59/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f4])).
% 1.59/0.64  fof(f4,axiom,(
% 1.59/0.64    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.59/0.64  fof(f307,plain,(
% 1.59/0.64    ~r1_tarski(k1_xboole_0,sK3) | sP0(sK3,sK2) | ~v2_tex_2(sK3,sK2) | (spl5_1 | ~spl5_3)),
% 1.59/0.64    inference(superposition,[],[f116,f299])).
% 1.59/0.64  fof(f299,plain,(
% 1.59/0.64    k1_xboole_0 = sK4(sK3,sK2) | (spl5_1 | ~spl5_3)),
% 1.59/0.64    inference(subsumption_resolution,[],[f298,f48])).
% 1.59/0.64  fof(f48,plain,(
% 1.59/0.64    ~v1_xboole_0(sK3)),
% 1.59/0.64    inference(cnf_transformation,[],[f34])).
% 1.59/0.64  fof(f298,plain,(
% 1.59/0.64    v1_xboole_0(sK3) | k1_xboole_0 = sK4(sK3,sK2) | (spl5_1 | ~spl5_3)),
% 1.59/0.64    inference(subsumption_resolution,[],[f297,f47])).
% 1.59/0.64  fof(f297,plain,(
% 1.59/0.64    ~l1_pre_topc(sK2) | v1_xboole_0(sK3) | k1_xboole_0 = sK4(sK3,sK2) | (spl5_1 | ~spl5_3)),
% 1.59/0.64    inference(subsumption_resolution,[],[f296,f46])).
% 1.59/0.64  fof(f46,plain,(
% 1.59/0.64    v2_tdlat_3(sK2)),
% 1.59/0.64    inference(cnf_transformation,[],[f34])).
% 1.59/0.64  fof(f296,plain,(
% 1.59/0.64    ~v2_tdlat_3(sK2) | ~l1_pre_topc(sK2) | v1_xboole_0(sK3) | k1_xboole_0 = sK4(sK3,sK2) | (spl5_1 | ~spl5_3)),
% 1.59/0.64    inference(subsumption_resolution,[],[f295,f102])).
% 1.59/0.64  fof(f295,plain,(
% 1.59/0.64    sP0(sK3,sK2) | ~v2_tdlat_3(sK2) | ~l1_pre_topc(sK2) | v1_xboole_0(sK3) | k1_xboole_0 = sK4(sK3,sK2) | ~spl5_3),
% 1.59/0.64    inference(subsumption_resolution,[],[f294,f44])).
% 1.59/0.64  fof(f44,plain,(
% 1.59/0.64    ~v2_struct_0(sK2)),
% 1.59/0.64    inference(cnf_transformation,[],[f34])).
% 1.59/0.64  fof(f294,plain,(
% 1.59/0.64    v2_struct_0(sK2) | sP0(sK3,sK2) | ~v2_tdlat_3(sK2) | ~l1_pre_topc(sK2) | v1_xboole_0(sK3) | k1_xboole_0 = sK4(sK3,sK2) | ~spl5_3),
% 1.59/0.64    inference(resolution,[],[f289,f141])).
% 1.59/0.64  fof(f289,plain,(
% 1.59/0.64    ( ! [X6,X5] : (~v2_tex_2(X6,X5) | v2_struct_0(X5) | sP0(X6,X5) | ~v2_tdlat_3(X5) | ~l1_pre_topc(X5) | v1_xboole_0(X6) | k1_xboole_0 = sK4(X6,X5)) )),
% 1.59/0.64    inference(resolution,[],[f194,f91])).
% 1.59/0.64  fof(f91,plain,(
% 1.59/0.64    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.59/0.64    inference(resolution,[],[f74,f52])).
% 1.59/0.64  fof(f52,plain,(
% 1.59/0.64    v1_xboole_0(k1_xboole_0)),
% 1.59/0.64    inference(cnf_transformation,[],[f1])).
% 1.59/0.64  fof(f1,axiom,(
% 1.59/0.64    v1_xboole_0(k1_xboole_0)),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.59/0.64  fof(f74,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f26])).
% 1.59/0.64  fof(f26,plain,(
% 1.59/0.64    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.59/0.64    inference(ennf_transformation,[],[f7])).
% 1.59/0.64  fof(f7,axiom,(
% 1.59/0.64    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.59/0.64  fof(f194,plain,(
% 1.59/0.64    ( ! [X0,X1] : (v1_xboole_0(sK4(X1,X0)) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | sP0(X1,X0) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1)) )),
% 1.59/0.64    inference(duplicate_literal_removal,[],[f192])).
% 1.59/0.64  fof(f192,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | sP0(X1,X0) | ~v2_tex_2(X1,X0) | v1_xboole_0(sK4(X1,X0)) | v1_xboole_0(X1) | sP0(X1,X0) | ~v2_tex_2(X1,X0)) )),
% 1.59/0.64    inference(resolution,[],[f170,f125])).
% 1.59/0.64  fof(f125,plain,(
% 1.59/0.64    ( ! [X2,X3] : (~v1_zfmisc_1(sK4(X2,X3)) | v1_xboole_0(sK4(X2,X3)) | v1_xboole_0(X2) | sP0(X2,X3) | ~v2_tex_2(X2,X3)) )),
% 1.59/0.64    inference(subsumption_resolution,[],[f119,f63])).
% 1.59/0.64  fof(f63,plain,(
% 1.59/0.64    ( ! [X0,X1] : (r1_tarski(X0,sK4(X0,X1)) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f40])).
% 1.59/0.64  fof(f40,plain,(
% 1.59/0.64    ! [X0,X1] : ((sP0(X0,X1) | (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 1.59/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 1.59/0.64  fof(f39,plain,(
% 1.59/0.64    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK4(X0,X1) != X0 & r1_tarski(X0,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.59/0.64    introduced(choice_axiom,[])).
% 1.59/0.64  fof(f38,plain,(
% 1.59/0.64    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_tex_2(X0,X1)) & ((! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_tex_2(X0,X1)) | ~sP0(X0,X1)))),
% 1.59/0.64    inference(rectify,[],[f37])).
% 1.59/0.64  fof(f37,plain,(
% 1.59/0.64    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 1.59/0.64    inference(flattening,[],[f36])).
% 1.59/0.64  fof(f36,plain,(
% 1.59/0.64    ! [X1,X0] : ((sP0(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~sP0(X1,X0)))),
% 1.59/0.64    inference(nnf_transformation,[],[f27])).
% 1.59/0.64  fof(f119,plain,(
% 1.59/0.64    ( ! [X2,X3] : (~r1_tarski(X2,sK4(X2,X3)) | ~v1_zfmisc_1(sK4(X2,X3)) | v1_xboole_0(sK4(X2,X3)) | v1_xboole_0(X2) | sP0(X2,X3) | ~v2_tex_2(X2,X3)) )),
% 1.59/0.64    inference(extensionality_resolution,[],[f55,f64])).
% 1.59/0.64  fof(f64,plain,(
% 1.59/0.64    ( ! [X0,X1] : (sK4(X0,X1) != X0 | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f40])).
% 1.59/0.64  fof(f55,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f18])).
% 1.59/0.64  fof(f18,plain,(
% 1.59/0.64    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.59/0.64    inference(flattening,[],[f17])).
% 1.59/0.64  fof(f17,plain,(
% 1.59/0.64    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.59/0.64    inference(ennf_transformation,[],[f11])).
% 1.59/0.64  fof(f11,axiom,(
% 1.59/0.64    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.59/0.64  fof(f170,plain,(
% 1.59/0.64    ( ! [X0,X1] : (v1_zfmisc_1(sK4(X0,X1)) | ~l1_pre_topc(X1) | ~v2_tdlat_3(X1) | v2_struct_0(X1) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.59/0.64    inference(subsumption_resolution,[],[f169,f62])).
% 1.59/0.64  fof(f62,plain,(
% 1.59/0.64    ( ! [X0,X1] : (v2_tex_2(sK4(X0,X1),X1) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f40])).
% 1.59/0.64  fof(f169,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~v2_tex_2(sK4(X0,X1),X1) | v1_zfmisc_1(sK4(X0,X1)) | ~l1_pre_topc(X1) | ~v2_tdlat_3(X1) | v2_struct_0(X1) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.59/0.64    inference(resolution,[],[f154,f61])).
% 1.59/0.64  fof(f61,plain,(
% 1.59/0.64    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f40])).
% 1.59/0.64  fof(f154,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_zfmisc_1(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.59/0.64    inference(subsumption_resolution,[],[f153,f66])).
% 1.59/0.64  fof(f66,plain,(
% 1.59/0.64    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f23])).
% 1.59/0.64  fof(f23,plain,(
% 1.59/0.64    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.59/0.64    inference(ennf_transformation,[],[f8])).
% 1.59/0.64  fof(f8,axiom,(
% 1.59/0.64    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 1.59/0.64  fof(f153,plain,(
% 1.59/0.64    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.59/0.64    inference(subsumption_resolution,[],[f67,f56])).
% 1.59/0.64  fof(f56,plain,(
% 1.59/0.64    ( ! [X0] : (~v2_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f20])).
% 1.59/0.64  fof(f20,plain,(
% 1.59/0.64    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.59/0.64    inference(flattening,[],[f19])).
% 1.59/0.64  fof(f19,plain,(
% 1.59/0.64    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.59/0.64    inference(ennf_transformation,[],[f9])).
% 1.59/0.64  fof(f9,axiom,(
% 1.59/0.64    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.59/0.64  fof(f67,plain,(
% 1.59/0.64    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f41])).
% 1.59/0.64  fof(f41,plain,(
% 1.59/0.64    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.59/0.64    inference(nnf_transformation,[],[f25])).
% 1.59/0.64  fof(f25,plain,(
% 1.59/0.64    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.59/0.64    inference(flattening,[],[f24])).
% 1.59/0.64  fof(f24,plain,(
% 1.59/0.64    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.59/0.64    inference(ennf_transformation,[],[f12])).
% 1.59/0.64  fof(f12,axiom,(
% 1.59/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 1.59/0.64  fof(f116,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~r1_tarski(sK4(X0,X1),X0) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.59/0.64    inference(subsumption_resolution,[],[f112,f63])).
% 1.59/0.64  fof(f112,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~r1_tarski(X0,sK4(X0,X1)) | ~r1_tarski(sK4(X0,X1),X0) | sP0(X0,X1) | ~v2_tex_2(X0,X1)) )),
% 1.59/0.64    inference(extensionality_resolution,[],[f73,f64])).
% 1.59/0.64  fof(f73,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f43])).
% 1.59/0.64  fof(f43,plain,(
% 1.59/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.64    inference(flattening,[],[f42])).
% 1.59/0.64  fof(f42,plain,(
% 1.59/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.59/0.64    inference(nnf_transformation,[],[f2])).
% 1.59/0.64  fof(f2,axiom,(
% 1.59/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.59/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.59/0.64  fof(f212,plain,(
% 1.59/0.64    spl5_3 | ~spl5_2),
% 1.59/0.64    inference(avatar_split_clause,[],[f211,f83,f140])).
% 1.59/0.64  fof(f83,plain,(
% 1.59/0.64    spl5_2 <=> v1_zfmisc_1(sK3)),
% 1.59/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.59/0.64  fof(f211,plain,(
% 1.59/0.64    ~v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2)),
% 1.59/0.64    inference(subsumption_resolution,[],[f210,f44])).
% 1.59/0.64  fof(f210,plain,(
% 1.59/0.64    ~v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2) | v2_struct_0(sK2)),
% 1.59/0.64    inference(subsumption_resolution,[],[f209,f46])).
% 1.59/0.64  fof(f209,plain,(
% 1.59/0.64    ~v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2)),
% 1.59/0.64    inference(subsumption_resolution,[],[f208,f47])).
% 1.59/0.64  fof(f208,plain,(
% 1.59/0.64    ~v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2)),
% 1.59/0.64    inference(subsumption_resolution,[],[f172,f48])).
% 1.59/0.64  fof(f172,plain,(
% 1.59/0.64    ~v1_zfmisc_1(sK3) | v2_tex_2(sK3,sK2) | v1_xboole_0(sK3) | ~l1_pre_topc(sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2)),
% 1.59/0.64    inference(resolution,[],[f171,f49])).
% 1.59/0.64  fof(f171,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.59/0.64    inference(subsumption_resolution,[],[f68,f56])).
% 1.59/0.64  fof(f68,plain,(
% 1.59/0.64    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f41])).
% 1.59/0.64  fof(f203,plain,(
% 1.59/0.64    spl5_2 | ~spl5_5),
% 1.59/0.64    inference(avatar_contradiction_clause,[],[f202])).
% 1.59/0.64  fof(f202,plain,(
% 1.59/0.64    $false | (spl5_2 | ~spl5_5)),
% 1.59/0.64    inference(subsumption_resolution,[],[f195,f201])).
% 1.59/0.64  fof(f201,plain,(
% 1.59/0.64    ~v2_tex_2(sK3,sK2) | spl5_2),
% 1.59/0.64    inference(subsumption_resolution,[],[f200,f44])).
% 1.59/0.64  fof(f200,plain,(
% 1.59/0.64    ~v2_tex_2(sK3,sK2) | v2_struct_0(sK2) | spl5_2),
% 1.59/0.64    inference(subsumption_resolution,[],[f199,f46])).
% 1.59/0.64  fof(f199,plain,(
% 1.59/0.64    ~v2_tex_2(sK3,sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2) | spl5_2),
% 1.59/0.64    inference(subsumption_resolution,[],[f198,f47])).
% 1.59/0.64  fof(f198,plain,(
% 1.59/0.64    ~v2_tex_2(sK3,sK2) | ~l1_pre_topc(sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2) | spl5_2),
% 1.59/0.64    inference(subsumption_resolution,[],[f168,f85])).
% 1.59/0.64  fof(f85,plain,(
% 1.59/0.64    ~v1_zfmisc_1(sK3) | spl5_2),
% 1.59/0.64    inference(avatar_component_clause,[],[f83])).
% 1.59/0.64  fof(f168,plain,(
% 1.59/0.64    ~v2_tex_2(sK3,sK2) | v1_zfmisc_1(sK3) | ~l1_pre_topc(sK2) | ~v2_tdlat_3(sK2) | v2_struct_0(sK2)),
% 1.59/0.64    inference(resolution,[],[f154,f49])).
% 1.59/0.64  fof(f195,plain,(
% 1.59/0.64    v2_tex_2(sK3,sK2) | ~spl5_5),
% 1.59/0.64    inference(resolution,[],[f184,f59])).
% 1.59/0.64  fof(f59,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~sP0(X0,X1) | v2_tex_2(X0,X1)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f40])).
% 1.59/0.64  fof(f184,plain,(
% 1.59/0.64    sP0(sK3,sK2) | ~spl5_5),
% 1.59/0.64    inference(avatar_component_clause,[],[f182])).
% 1.59/0.64  fof(f182,plain,(
% 1.59/0.64    spl5_5 <=> sP0(sK3,sK2)),
% 1.59/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.59/0.64  fof(f185,plain,(
% 1.59/0.64    spl5_5 | ~spl5_1),
% 1.59/0.64    inference(avatar_split_clause,[],[f101,f79,f182])).
% 1.59/0.64  fof(f101,plain,(
% 1.59/0.64    ~v3_tex_2(sK3,sK2) | sP0(sK3,sK2)),
% 1.59/0.64    inference(resolution,[],[f99,f57])).
% 1.59/0.64  fof(f57,plain,(
% 1.59/0.64    ( ! [X0,X1] : (~sP1(X0,X1) | ~v3_tex_2(X1,X0) | sP0(X1,X0)) )),
% 1.59/0.64    inference(cnf_transformation,[],[f35])).
% 1.59/0.64  fof(f87,plain,(
% 1.59/0.64    spl5_1 | spl5_2),
% 1.59/0.64    inference(avatar_split_clause,[],[f50,f83,f79])).
% 1.59/0.64  fof(f50,plain,(
% 1.59/0.64    v1_zfmisc_1(sK3) | v3_tex_2(sK3,sK2)),
% 1.59/0.64    inference(cnf_transformation,[],[f34])).
% 1.59/0.64  fof(f86,plain,(
% 1.59/0.64    ~spl5_1 | ~spl5_2),
% 1.59/0.64    inference(avatar_split_clause,[],[f51,f83,f79])).
% 1.59/0.64  fof(f51,plain,(
% 1.59/0.64    ~v1_zfmisc_1(sK3) | ~v3_tex_2(sK3,sK2)),
% 1.59/0.64    inference(cnf_transformation,[],[f34])).
% 1.59/0.64  % SZS output end Proof for theBenchmark
% 1.59/0.64  % (28453)------------------------------
% 1.59/0.64  % (28453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.64  % (28453)Termination reason: Refutation
% 1.59/0.64  
% 1.59/0.64  % (28453)Memory used [KB]: 10874
% 1.59/0.64  % (28453)Time elapsed: 0.207 s
% 1.59/0.64  % (28453)------------------------------
% 1.59/0.64  % (28453)------------------------------
% 1.59/0.64  % (28446)Success in time 0.274 s
%------------------------------------------------------------------------------
