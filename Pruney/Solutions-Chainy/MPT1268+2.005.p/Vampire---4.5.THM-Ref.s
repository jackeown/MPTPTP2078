%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:26 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 388 expanded)
%              Number of leaves         :   25 ( 128 expanded)
%              Depth                    :   19
%              Number of atoms          :  508 (3402 expanded)
%              Number of equality atoms :   74 ( 530 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f607,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f121,f128,f183,f304,f323,f408,f606])).

fof(f606,plain,
    ( spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_21
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_21
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f604,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f604,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_21
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f601,f101])).

fof(f101,plain,
    ( k1_xboole_0 != sK3
    | spl6_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f601,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_21
    | ~ spl6_29 ),
    inference(resolution,[],[f596,f186])).

fof(f186,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | X2 = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f175,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f79,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f175,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X1,X0)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f88,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f596,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_21
    | ~ spl6_29 ),
    inference(forward_demodulation,[],[f595,f398])).

fof(f398,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl6_29
  <=> sK3 = k1_tops_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f595,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f591,f111])).

fof(f111,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_4
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f591,plain,
    ( ~ r1_tarski(sK3,sK2)
    | r1_tarski(k1_tops_1(sK1,sK3),k1_xboole_0)
    | ~ spl6_5
    | ~ spl6_21 ),
    inference(resolution,[],[f458,f116])).

fof(f116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f458,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,sK2)
        | r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0) )
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f457,f55])).

fof(f55,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ( k1_xboole_0 != sK3
        & v3_pre_topc(sK3,sK1)
        & r1_tarski(sK3,sK2)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | ~ v2_tops_1(sK2,sK1) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK1)
          | ~ r1_tarski(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      | v2_tops_1(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK1)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
            | ~ v2_tops_1(X1,sK1) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK1)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            | v2_tops_1(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK1)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          | ~ v2_tops_1(X1,sK1) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK1)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          | v2_tops_1(X1,sK1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK1)
            & r1_tarski(X2,sK2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
        | ~ v2_tops_1(sK2,sK1) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK1)
            | ~ r1_tarski(X3,sK2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        | v2_tops_1(sK2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK1)
        & r1_tarski(X2,sK2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k1_xboole_0 != sK3
      & v3_pre_topc(sK3,sK1)
      & r1_tarski(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f40])).

% (7976)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (7978)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f457,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0)
        | ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f444,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f444,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0)
        | ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl6_21 ),
    inference(superposition,[],[f66,f319])).

fof(f319,plain,
    ( k1_xboole_0 = k1_tops_1(sK1,sK2)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl6_21
  <=> k1_xboole_0 = k1_tops_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f408,plain,
    ( spl6_29
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f407,f126,f114,f104,f396])).

fof(f104,plain,
    ( spl6_3
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f126,plain,
    ( spl6_8
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f407,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f406,f106])).

fof(f106,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f406,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ v3_pre_topc(sK3,sK1)
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f403,f55])).

fof(f403,plain,
    ( ~ l1_pre_topc(sK1)
    | sK3 = k1_tops_1(sK1,sK3)
    | ~ v3_pre_topc(sK3,sK1)
    | ~ spl6_5
    | ~ spl6_8 ),
    inference(resolution,[],[f127,f116])).

fof(f127,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f323,plain,
    ( spl6_21
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f322,f95,f318])).

fof(f95,plain,
    ( spl6_1
  <=> v2_tops_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f322,plain,
    ( ~ v2_tops_1(sK2,sK1)
    | k1_xboole_0 = k1_tops_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f264,f55])).

fof(f264,plain,
    ( ~ v2_tops_1(sK2,sK1)
    | k1_xboole_0 = k1_tops_1(sK1,sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f64,f56])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f304,plain,
    ( spl6_1
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl6_1
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f302,f229])).

fof(f229,plain,(
    r1_tarski(k1_tops_1(sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f225,f55])).

fof(f225,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f63,f56])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f302,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
    | spl6_1
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f299,f293])).

fof(f293,plain,
    ( k1_xboole_0 != k1_tops_1(sK1,sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f292,f55])).

fof(f292,plain,
    ( k1_xboole_0 != k1_tops_1(sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f288,f97])).

fof(f97,plain,
    ( ~ v2_tops_1(sK2,sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f288,plain,
    ( k1_xboole_0 != k1_tops_1(sK1,sK2)
    | v2_tops_1(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f65,f56])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f299,plain,
    ( k1_xboole_0 = k1_tops_1(sK1,sK2)
    | ~ r1_tarski(k1_tops_1(sK1,sK2),sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f251,f56])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k1_xboole_0 = k1_tops_1(sK1,X0)
        | ~ r1_tarski(k1_tops_1(sK1,X0),sK2) )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f250,f54])).

fof(f54,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_pre_topc(sK1)
        | k1_xboole_0 = k1_tops_1(sK1,X0)
        | ~ r1_tarski(k1_tops_1(sK1,X0),sK2) )
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f249,f55])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | k1_xboole_0 = k1_tops_1(sK1,X0)
        | ~ r1_tarski(k1_tops_1(sK1,X0),sK2) )
    | ~ spl6_6 ),
    inference(resolution,[],[f80,f173])).

fof(f173,plain,
    ( ! [X4] :
        ( ~ v3_pre_topc(X4,sK1)
        | k1_xboole_0 = X4
        | ~ r1_tarski(X4,sK2) )
    | ~ spl6_6 ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,sK2)
        | k1_xboole_0 = X4
        | ~ r1_tarski(X4,sK2)
        | ~ v3_pre_topc(X4,sK1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f167,f144])).

fof(f144,plain,(
    r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f81,f56])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,u1_struct_0(sK1))
        | ~ r1_tarski(X1,X0)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,sK2)
        | ~ v3_pre_topc(X1,sK1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f85,f145])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK1))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK2)
        | ~ v3_pre_topc(X0,sK1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f82,f120])).

fof(f120,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK1) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_6
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X3,sK2)
        | ~ v3_pre_topc(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f183,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f181,f55])).

fof(f181,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f177,f54])).

fof(f177,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f124,f56])).

fof(f124,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_7
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f128,plain,
    ( spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f69,f126,f123])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f121,plain,
    ( spl6_1
    | spl6_6 ),
    inference(avatar_split_clause,[],[f57,f119,f95])).

fof(f57,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK1)
      | ~ r1_tarski(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | v2_tops_1(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f117,plain,
    ( ~ spl6_1
    | spl6_5 ),
    inference(avatar_split_clause,[],[f58,f114,f95])).

fof(f58,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,
    ( ~ spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f59,f109,f95])).

fof(f59,plain,
    ( r1_tarski(sK3,sK2)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f60,f104,f95])).

fof(f60,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f61,f99,f95])).

fof(f61,plain,
    ( k1_xboole_0 != sK3
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:55:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.49/0.57  % (7983)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.57  % (7975)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.49/0.58  % (7967)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.58  % (7973)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.49/0.59  % (7989)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.59  % (7981)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.49/0.59  % (7969)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.49/0.59  % (7962)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.49/0.60  % (7961)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.49/0.60  % (7964)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.49/0.60  % (7979)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.60  % (7966)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.49/0.61  % (7987)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.49/0.61  % (7968)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.61  % (7963)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.49/0.61  % (7971)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.62  % (7974)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.49/0.62  % (7977)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.62  % (7982)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.49/0.63  % (7960)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.49/0.63  % (7988)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.64  % (7972)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.17/0.64  % (7965)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 2.17/0.64  % (7980)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.17/0.64  % (7984)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.17/0.65  % (7985)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.17/0.66  % (7970)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.17/0.66  % (7987)Refutation found. Thanks to Tanya!
% 2.17/0.66  % SZS status Theorem for theBenchmark
% 2.17/0.66  % SZS output start Proof for theBenchmark
% 2.17/0.66  fof(f607,plain,(
% 2.17/0.66    $false),
% 2.17/0.66    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f121,f128,f183,f304,f323,f408,f606])).
% 2.17/0.66  fof(f606,plain,(
% 2.17/0.66    spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_21 | ~spl6_29),
% 2.17/0.66    inference(avatar_contradiction_clause,[],[f605])).
% 2.17/0.66  fof(f605,plain,(
% 2.17/0.66    $false | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_21 | ~spl6_29)),
% 2.17/0.66    inference(subsumption_resolution,[],[f604,f62])).
% 2.17/0.66  fof(f62,plain,(
% 2.17/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f5])).
% 2.17/0.66  fof(f5,axiom,(
% 2.17/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.17/0.66  fof(f604,plain,(
% 2.17/0.66    ~r1_tarski(k1_xboole_0,sK3) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_21 | ~spl6_29)),
% 2.17/0.66    inference(subsumption_resolution,[],[f601,f101])).
% 2.17/0.66  fof(f101,plain,(
% 2.17/0.66    k1_xboole_0 != sK3 | spl6_2),
% 2.17/0.66    inference(avatar_component_clause,[],[f99])).
% 2.17/0.66  fof(f99,plain,(
% 2.17/0.66    spl6_2 <=> k1_xboole_0 = sK3),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.17/0.66  fof(f601,plain,(
% 2.17/0.66    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | (~spl6_4 | ~spl6_5 | ~spl6_21 | ~spl6_29)),
% 2.17/0.66    inference(resolution,[],[f596,f186])).
% 2.17/0.66  fof(f186,plain,(
% 2.17/0.66    ( ! [X2,X3] : (~r1_tarski(X3,X2) | X2 = X3 | ~r1_tarski(X2,X3)) )),
% 2.17/0.66    inference(superposition,[],[f175,f88])).
% 2.17/0.66  fof(f88,plain,(
% 2.17/0.66    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.17/0.66    inference(definition_unfolding,[],[f79,f76])).
% 2.17/0.66  fof(f76,plain,(
% 2.17/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.17/0.66    inference(cnf_transformation,[],[f8])).
% 2.17/0.66  fof(f8,axiom,(
% 2.17/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.17/0.66  fof(f79,plain,(
% 2.17/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f30])).
% 2.17/0.66  fof(f30,plain,(
% 2.17/0.66    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.17/0.66    inference(ennf_transformation,[],[f4])).
% 2.17/0.66  fof(f4,axiom,(
% 2.17/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.17/0.66  fof(f175,plain,(
% 2.17/0.66    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.17/0.66    inference(superposition,[],[f88,f75])).
% 2.17/0.66  fof(f75,plain,(
% 2.17/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.17/0.66    inference(cnf_transformation,[],[f7])).
% 2.17/0.66  fof(f7,axiom,(
% 2.17/0.66    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.17/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.17/0.66  fof(f596,plain,(
% 2.17/0.66    r1_tarski(sK3,k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_21 | ~spl6_29)),
% 2.17/0.66    inference(forward_demodulation,[],[f595,f398])).
% 2.17/0.66  fof(f398,plain,(
% 2.17/0.66    sK3 = k1_tops_1(sK1,sK3) | ~spl6_29),
% 2.17/0.66    inference(avatar_component_clause,[],[f396])).
% 2.17/0.66  fof(f396,plain,(
% 2.17/0.66    spl6_29 <=> sK3 = k1_tops_1(sK1,sK3)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.17/0.66  fof(f595,plain,(
% 2.17/0.66    r1_tarski(k1_tops_1(sK1,sK3),k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_21)),
% 2.17/0.66    inference(subsumption_resolution,[],[f591,f111])).
% 2.17/0.66  fof(f111,plain,(
% 2.17/0.66    r1_tarski(sK3,sK2) | ~spl6_4),
% 2.17/0.66    inference(avatar_component_clause,[],[f109])).
% 2.17/0.66  fof(f109,plain,(
% 2.17/0.66    spl6_4 <=> r1_tarski(sK3,sK2)),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.17/0.66  fof(f591,plain,(
% 2.17/0.66    ~r1_tarski(sK3,sK2) | r1_tarski(k1_tops_1(sK1,sK3),k1_xboole_0) | (~spl6_5 | ~spl6_21)),
% 2.17/0.66    inference(resolution,[],[f458,f116])).
% 2.17/0.66  fof(f116,plain,(
% 2.17/0.66    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl6_5),
% 2.17/0.66    inference(avatar_component_clause,[],[f114])).
% 2.17/0.66  fof(f114,plain,(
% 2.17/0.66    spl6_5 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 2.17/0.66  fof(f458,plain,(
% 2.17/0.66    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,sK2) | r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0)) ) | ~spl6_21),
% 2.17/0.66    inference(subsumption_resolution,[],[f457,f55])).
% 2.17/0.66  fof(f55,plain,(
% 2.17/0.66    l1_pre_topc(sK1)),
% 2.17/0.66    inference(cnf_transformation,[],[f45])).
% 2.17/0.66  fof(f45,plain,(
% 2.17/0.66    (((k1_xboole_0 != sK3 & v3_pre_topc(sK3,sK1) & r1_tarski(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) | ~v2_tops_1(sK2,sK1)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK1) | ~r1_tarski(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | v2_tops_1(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 2.17/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f44,f43,f42])).
% 2.17/0.66  fof(f42,plain,(
% 2.17/0.66    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK1) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) | ~v2_tops_1(X1,sK1)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK1) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | v2_tops_1(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.17/0.66    introduced(choice_axiom,[])).
% 2.17/0.66  fof(f43,plain,(
% 2.17/0.66    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK1) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) | ~v2_tops_1(X1,sK1)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK1) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | v2_tops_1(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK1) & r1_tarski(X2,sK2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) | ~v2_tops_1(sK2,sK1)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK1) | ~r1_tarski(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) | v2_tops_1(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 2.17/0.66    introduced(choice_axiom,[])).
% 2.17/0.66  fof(f44,plain,(
% 2.17/0.66    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK1) & r1_tarski(X2,sK2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) => (k1_xboole_0 != sK3 & v3_pre_topc(sK3,sK1) & r1_tarski(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 2.17/0.66    introduced(choice_axiom,[])).
% 2.17/0.66  fof(f41,plain,(
% 2.17/0.66    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.17/0.66    inference(rectify,[],[f40])).
% 2.17/0.66  % (7976)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.17/0.66  % (7978)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.17/0.68  fof(f40,plain,(
% 2.17/0.68    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.17/0.68    inference(flattening,[],[f39])).
% 2.17/0.68  fof(f39,plain,(
% 2.17/0.68    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.17/0.68    inference(nnf_transformation,[],[f21])).
% 2.17/0.68  fof(f21,plain,(
% 2.17/0.68    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.17/0.68    inference(flattening,[],[f20])).
% 2.17/0.68  fof(f20,plain,(
% 2.17/0.68    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.17/0.68    inference(ennf_transformation,[],[f19])).
% 2.17/0.68  fof(f19,negated_conjecture,(
% 2.17/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.17/0.68    inference(negated_conjecture,[],[f18])).
% 2.17/0.68  fof(f18,conjecture,(
% 2.17/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).
% 2.17/0.68  fof(f457,plain,(
% 2.17/0.68    ( ! [X0] : (r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0) | ~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) ) | ~spl6_21),
% 2.17/0.68    inference(subsumption_resolution,[],[f444,f56])).
% 2.17/0.68  fof(f56,plain,(
% 2.17/0.68    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.17/0.68    inference(cnf_transformation,[],[f45])).
% 2.17/0.68  fof(f444,plain,(
% 2.17/0.68    ( ! [X0] : (r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0) | ~r1_tarski(X0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) ) | ~spl6_21),
% 2.17/0.68    inference(superposition,[],[f66,f319])).
% 2.17/0.68  fof(f319,plain,(
% 2.17/0.68    k1_xboole_0 = k1_tops_1(sK1,sK2) | ~spl6_21),
% 2.17/0.68    inference(avatar_component_clause,[],[f318])).
% 2.17/0.68  fof(f318,plain,(
% 2.17/0.68    spl6_21 <=> k1_xboole_0 = k1_tops_1(sK1,sK2)),
% 2.17/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 2.17/0.68  fof(f66,plain,(
% 2.17/0.68    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f25])).
% 2.17/0.68  fof(f25,plain,(
% 2.17/0.68    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.68    inference(flattening,[],[f24])).
% 2.17/0.68  fof(f24,plain,(
% 2.17/0.68    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.68    inference(ennf_transformation,[],[f15])).
% 2.17/0.68  fof(f15,axiom,(
% 2.17/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 2.17/0.68  fof(f408,plain,(
% 2.17/0.68    spl6_29 | ~spl6_3 | ~spl6_5 | ~spl6_8),
% 2.17/0.68    inference(avatar_split_clause,[],[f407,f126,f114,f104,f396])).
% 2.17/0.68  fof(f104,plain,(
% 2.17/0.68    spl6_3 <=> v3_pre_topc(sK3,sK1)),
% 2.17/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.17/0.68  fof(f126,plain,(
% 2.17/0.68    spl6_8 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 2.17/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 2.17/0.68  fof(f407,plain,(
% 2.17/0.68    sK3 = k1_tops_1(sK1,sK3) | (~spl6_3 | ~spl6_5 | ~spl6_8)),
% 2.17/0.68    inference(subsumption_resolution,[],[f406,f106])).
% 2.17/0.68  fof(f106,plain,(
% 2.17/0.68    v3_pre_topc(sK3,sK1) | ~spl6_3),
% 2.17/0.68    inference(avatar_component_clause,[],[f104])).
% 2.17/0.68  fof(f406,plain,(
% 2.17/0.68    sK3 = k1_tops_1(sK1,sK3) | ~v3_pre_topc(sK3,sK1) | (~spl6_5 | ~spl6_8)),
% 2.17/0.68    inference(subsumption_resolution,[],[f403,f55])).
% 2.17/0.68  fof(f403,plain,(
% 2.17/0.68    ~l1_pre_topc(sK1) | sK3 = k1_tops_1(sK1,sK3) | ~v3_pre_topc(sK3,sK1) | (~spl6_5 | ~spl6_8)),
% 2.17/0.68    inference(resolution,[],[f127,f116])).
% 2.17/0.68  fof(f127,plain,(
% 2.17/0.68    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl6_8),
% 2.17/0.68    inference(avatar_component_clause,[],[f126])).
% 2.17/0.68  fof(f323,plain,(
% 2.17/0.68    spl6_21 | ~spl6_1),
% 2.17/0.68    inference(avatar_split_clause,[],[f322,f95,f318])).
% 2.17/0.68  fof(f95,plain,(
% 2.17/0.68    spl6_1 <=> v2_tops_1(sK2,sK1)),
% 2.17/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.17/0.68  fof(f322,plain,(
% 2.17/0.68    ~v2_tops_1(sK2,sK1) | k1_xboole_0 = k1_tops_1(sK1,sK2)),
% 2.17/0.68    inference(subsumption_resolution,[],[f264,f55])).
% 2.17/0.68  fof(f264,plain,(
% 2.17/0.68    ~v2_tops_1(sK2,sK1) | k1_xboole_0 = k1_tops_1(sK1,sK2) | ~l1_pre_topc(sK1)),
% 2.17/0.68    inference(resolution,[],[f64,f56])).
% 2.17/0.68  fof(f64,plain,(
% 2.17/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f46])).
% 2.17/0.68  fof(f46,plain,(
% 2.17/0.68    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.68    inference(nnf_transformation,[],[f23])).
% 2.17/0.68  fof(f23,plain,(
% 2.17/0.68    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.68    inference(ennf_transformation,[],[f17])).
% 2.17/0.68  fof(f17,axiom,(
% 2.17/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 2.17/0.68  fof(f304,plain,(
% 2.17/0.68    spl6_1 | ~spl6_6),
% 2.17/0.68    inference(avatar_contradiction_clause,[],[f303])).
% 2.17/0.68  fof(f303,plain,(
% 2.17/0.68    $false | (spl6_1 | ~spl6_6)),
% 2.17/0.68    inference(subsumption_resolution,[],[f302,f229])).
% 2.17/0.68  fof(f229,plain,(
% 2.17/0.68    r1_tarski(k1_tops_1(sK1,sK2),sK2)),
% 2.17/0.68    inference(subsumption_resolution,[],[f225,f55])).
% 2.17/0.68  fof(f225,plain,(
% 2.17/0.68    r1_tarski(k1_tops_1(sK1,sK2),sK2) | ~l1_pre_topc(sK1)),
% 2.17/0.68    inference(resolution,[],[f63,f56])).
% 2.17/0.68  fof(f63,plain,(
% 2.17/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f22])).
% 2.17/0.68  fof(f22,plain,(
% 2.17/0.68    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.17/0.68    inference(ennf_transformation,[],[f14])).
% 2.17/0.68  fof(f14,axiom,(
% 2.17/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.17/0.68  fof(f302,plain,(
% 2.17/0.68    ~r1_tarski(k1_tops_1(sK1,sK2),sK2) | (spl6_1 | ~spl6_6)),
% 2.17/0.68    inference(subsumption_resolution,[],[f299,f293])).
% 2.17/0.68  fof(f293,plain,(
% 2.17/0.68    k1_xboole_0 != k1_tops_1(sK1,sK2) | spl6_1),
% 2.17/0.68    inference(subsumption_resolution,[],[f292,f55])).
% 2.17/0.68  fof(f292,plain,(
% 2.17/0.68    k1_xboole_0 != k1_tops_1(sK1,sK2) | ~l1_pre_topc(sK1) | spl6_1),
% 2.17/0.68    inference(subsumption_resolution,[],[f288,f97])).
% 2.17/0.68  fof(f97,plain,(
% 2.17/0.68    ~v2_tops_1(sK2,sK1) | spl6_1),
% 2.17/0.68    inference(avatar_component_clause,[],[f95])).
% 2.17/0.68  fof(f288,plain,(
% 2.17/0.68    k1_xboole_0 != k1_tops_1(sK1,sK2) | v2_tops_1(sK2,sK1) | ~l1_pre_topc(sK1)),
% 2.17/0.68    inference(resolution,[],[f65,f56])).
% 2.17/0.68  fof(f65,plain,(
% 2.17/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f46])).
% 2.17/0.68  fof(f299,plain,(
% 2.17/0.68    k1_xboole_0 = k1_tops_1(sK1,sK2) | ~r1_tarski(k1_tops_1(sK1,sK2),sK2) | ~spl6_6),
% 2.17/0.68    inference(resolution,[],[f251,f56])).
% 2.17/0.68  fof(f251,plain,(
% 2.17/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k1_xboole_0 = k1_tops_1(sK1,X0) | ~r1_tarski(k1_tops_1(sK1,X0),sK2)) ) | ~spl6_6),
% 2.17/0.68    inference(subsumption_resolution,[],[f250,f54])).
% 2.17/0.68  fof(f54,plain,(
% 2.17/0.68    v2_pre_topc(sK1)),
% 2.17/0.68    inference(cnf_transformation,[],[f45])).
% 2.17/0.68  fof(f250,plain,(
% 2.17/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1) | k1_xboole_0 = k1_tops_1(sK1,X0) | ~r1_tarski(k1_tops_1(sK1,X0),sK2)) ) | ~spl6_6),
% 2.17/0.68    inference(subsumption_resolution,[],[f249,f55])).
% 2.17/0.68  fof(f249,plain,(
% 2.17/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | k1_xboole_0 = k1_tops_1(sK1,X0) | ~r1_tarski(k1_tops_1(sK1,X0),sK2)) ) | ~spl6_6),
% 2.17/0.68    inference(resolution,[],[f80,f173])).
% 2.17/0.68  fof(f173,plain,(
% 2.17/0.68    ( ! [X4] : (~v3_pre_topc(X4,sK1) | k1_xboole_0 = X4 | ~r1_tarski(X4,sK2)) ) | ~spl6_6),
% 2.17/0.68    inference(duplicate_literal_removal,[],[f171])).
% 2.17/0.68  fof(f171,plain,(
% 2.17/0.68    ( ! [X4] : (~r1_tarski(X4,sK2) | k1_xboole_0 = X4 | ~r1_tarski(X4,sK2) | ~v3_pre_topc(X4,sK1)) ) | ~spl6_6),
% 2.17/0.68    inference(resolution,[],[f167,f144])).
% 2.17/0.68  fof(f144,plain,(
% 2.17/0.68    r1_tarski(sK2,u1_struct_0(sK1))),
% 2.17/0.68    inference(resolution,[],[f81,f56])).
% 2.17/0.68  fof(f81,plain,(
% 2.17/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f53])).
% 2.17/0.68  fof(f53,plain,(
% 2.17/0.68    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.17/0.68    inference(nnf_transformation,[],[f9])).
% 2.17/0.68  fof(f9,axiom,(
% 2.17/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.17/0.68  fof(f167,plain,(
% 2.17/0.68    ( ! [X0,X1] : (~r1_tarski(X0,u1_struct_0(sK1)) | ~r1_tarski(X1,X0) | k1_xboole_0 = X1 | ~r1_tarski(X1,sK2) | ~v3_pre_topc(X1,sK1)) ) | ~spl6_6),
% 2.17/0.68    inference(resolution,[],[f85,f145])).
% 2.17/0.68  fof(f145,plain,(
% 2.17/0.68    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK1)) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK2) | ~v3_pre_topc(X0,sK1)) ) | ~spl6_6),
% 2.17/0.68    inference(resolution,[],[f82,f120])).
% 2.17/0.68  fof(f120,plain,(
% 2.17/0.68    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK1)) ) | ~spl6_6),
% 2.17/0.68    inference(avatar_component_clause,[],[f119])).
% 2.17/0.68  fof(f119,plain,(
% 2.17/0.68    spl6_6 <=> ! [X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK1))),
% 2.17/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 2.17/0.68  fof(f82,plain,(
% 2.17/0.68    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f53])).
% 2.17/0.68  fof(f85,plain,(
% 2.17/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f36])).
% 2.17/0.68  fof(f36,plain,(
% 2.17/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.17/0.68    inference(flattening,[],[f35])).
% 2.17/0.68  fof(f35,plain,(
% 2.17/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.17/0.68    inference(ennf_transformation,[],[f3])).
% 2.17/0.68  fof(f3,axiom,(
% 2.17/0.68    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.17/0.68  fof(f80,plain,(
% 2.17/0.68    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f32])).
% 2.17/0.68  fof(f32,plain,(
% 2.17/0.68    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.17/0.68    inference(flattening,[],[f31])).
% 2.17/0.68  fof(f31,plain,(
% 2.17/0.68    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.17/0.68    inference(ennf_transformation,[],[f12])).
% 2.17/0.68  fof(f12,axiom,(
% 2.17/0.68    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.17/0.68  fof(f183,plain,(
% 2.17/0.68    ~spl6_7),
% 2.17/0.68    inference(avatar_contradiction_clause,[],[f182])).
% 2.17/0.68  fof(f182,plain,(
% 2.17/0.68    $false | ~spl6_7),
% 2.17/0.68    inference(subsumption_resolution,[],[f181,f55])).
% 2.17/0.68  fof(f181,plain,(
% 2.17/0.68    ~l1_pre_topc(sK1) | ~spl6_7),
% 2.17/0.68    inference(subsumption_resolution,[],[f177,f54])).
% 2.17/0.68  fof(f177,plain,(
% 2.17/0.68    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~spl6_7),
% 2.17/0.68    inference(resolution,[],[f124,f56])).
% 2.17/0.68  fof(f124,plain,(
% 2.17/0.68    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl6_7),
% 2.17/0.68    inference(avatar_component_clause,[],[f123])).
% 2.17/0.68  fof(f123,plain,(
% 2.17/0.68    spl6_7 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.17/0.68    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 2.17/0.68  fof(f128,plain,(
% 2.17/0.68    spl6_7 | spl6_8),
% 2.17/0.68    inference(avatar_split_clause,[],[f69,f126,f123])).
% 2.17/0.68  fof(f69,plain,(
% 2.17/0.68    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f28])).
% 2.17/0.68  fof(f28,plain,(
% 2.17/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.17/0.68    inference(flattening,[],[f27])).
% 2.17/0.68  fof(f27,plain,(
% 2.17/0.68    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.17/0.68    inference(ennf_transformation,[],[f16])).
% 2.17/0.68  fof(f16,axiom,(
% 2.17/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.17/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 2.17/0.68  fof(f121,plain,(
% 2.17/0.68    spl6_1 | spl6_6),
% 2.17/0.68    inference(avatar_split_clause,[],[f57,f119,f95])).
% 2.17/0.68  fof(f57,plain,(
% 2.17/0.68    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK1) | ~r1_tarski(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | v2_tops_1(sK2,sK1)) )),
% 2.17/0.68    inference(cnf_transformation,[],[f45])).
% 2.17/0.68  fof(f117,plain,(
% 2.17/0.68    ~spl6_1 | spl6_5),
% 2.17/0.68    inference(avatar_split_clause,[],[f58,f114,f95])).
% 2.17/0.68  fof(f58,plain,(
% 2.17/0.68    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_tops_1(sK2,sK1)),
% 2.17/0.68    inference(cnf_transformation,[],[f45])).
% 2.17/0.68  fof(f112,plain,(
% 2.17/0.68    ~spl6_1 | spl6_4),
% 2.17/0.68    inference(avatar_split_clause,[],[f59,f109,f95])).
% 2.17/0.68  fof(f59,plain,(
% 2.17/0.68    r1_tarski(sK3,sK2) | ~v2_tops_1(sK2,sK1)),
% 2.17/0.68    inference(cnf_transformation,[],[f45])).
% 2.17/0.68  fof(f107,plain,(
% 2.17/0.68    ~spl6_1 | spl6_3),
% 2.17/0.68    inference(avatar_split_clause,[],[f60,f104,f95])).
% 2.17/0.68  fof(f60,plain,(
% 2.17/0.68    v3_pre_topc(sK3,sK1) | ~v2_tops_1(sK2,sK1)),
% 2.17/0.68    inference(cnf_transformation,[],[f45])).
% 2.17/0.68  fof(f102,plain,(
% 2.17/0.68    ~spl6_1 | ~spl6_2),
% 2.17/0.68    inference(avatar_split_clause,[],[f61,f99,f95])).
% 2.17/0.68  fof(f61,plain,(
% 2.17/0.68    k1_xboole_0 != sK3 | ~v2_tops_1(sK2,sK1)),
% 2.17/0.68    inference(cnf_transformation,[],[f45])).
% 2.17/0.68  % SZS output end Proof for theBenchmark
% 2.17/0.68  % (7987)------------------------------
% 2.17/0.68  % (7987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.68  % (7987)Termination reason: Refutation
% 2.17/0.68  
% 2.17/0.68  % (7987)Memory used [KB]: 6524
% 2.17/0.68  % (7987)Time elapsed: 0.211 s
% 2.17/0.68  % (7987)------------------------------
% 2.17/0.68  % (7987)------------------------------
% 2.17/0.68  % (7959)Success in time 0.311 s
%------------------------------------------------------------------------------
