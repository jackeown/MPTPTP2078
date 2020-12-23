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
% DateTime   : Thu Dec  3 13:12:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 326 expanded)
%              Number of leaves         :   25 ( 115 expanded)
%              Depth                    :   14
%              Number of atoms          :  421 (2748 expanded)
%              Number of equality atoms :   59 ( 426 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f76,f87,f122,f124,f129,f138,f141,f143,f210,f236])).

fof(f236,plain,
    ( spl3_2
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl3_2
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f58,f212])).

fof(f212,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f211,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f211,plain,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,k1_xboole_0))
    | ~ spl3_23 ),
    inference(resolution,[],[f209,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f209,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl3_23
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f58,plain,
    ( k1_xboole_0 != sK2
    | spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f210,plain,
    ( ~ spl3_4
    | ~ spl3_3
    | spl3_23
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f205,f85,f69,f208,f61,f65])).

fof(f65,plain,
    ( spl3_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f61,plain,
    ( spl3_3
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f69,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f85,plain,
    ( spl3_7
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f205,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ r1_tarski(sK2,sK1)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f188,f70])).

fof(f70,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(X0,k1_xboole_0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f82,f137])).

fof(f137,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | r1_tarski(X0,k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(global_subsumption,[],[f33,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ v3_pre_topc(X0,sK0)
      | r1_tarski(X0,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).

fof(f26,plain,
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
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_tops_1(X1,sK0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK0)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK0)
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_tops_1(sK1,sK0) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK0)
            | ~ r1_tarski(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK0)
        & r1_tarski(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK2
      & v3_pre_topc(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f143,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f142,f54,f85])).

fof(f54,plain,
    ( spl3_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f142,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(global_subsumption,[],[f33,f78])).

fof(f78,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f141,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl3_14 ),
    inference(subsumption_resolution,[],[f88,f136])).

fof(f136,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_14
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f88,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(global_subsumption,[],[f33,f80])).

fof(f80,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f138,plain,
    ( ~ spl3_14
    | spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f133,f120,f85,f135])).

fof(f120,plain,
    ( spl3_13
  <=> ! [X0] :
        ( k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f133,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_13 ),
    inference(resolution,[],[f121,f34])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f120])).

fof(f129,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl3_12 ),
    inference(subsumption_resolution,[],[f33,f118])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f124,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl3_11 ),
    inference(subsumption_resolution,[],[f32,f115])).

fof(f115,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_11
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f122,plain,
    ( ~ spl3_11
    | ~ spl3_12
    | spl3_13
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f112,f74,f120,f117,f114])).

fof(f74,plain,
    ( spl3_6
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f112,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_6 ),
    inference(resolution,[],[f111,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f111,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK0)
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1) )
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK0)
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1)
        | ~ r1_tarski(X3,sK1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f103,f81])).

fof(f81,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f34,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ v3_pre_topc(X0,sK0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f90,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl3_6 ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f87,plain,
    ( spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f83,f85,f54])).

fof(f83,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f33,f79])).

fof(f79,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f34,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,
    ( spl3_1
    | spl3_6 ),
    inference(avatar_split_clause,[],[f35,f74,f54])).

fof(f35,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,
    ( ~ spl3_1
    | spl3_5 ),
    inference(avatar_split_clause,[],[f36,f69,f54])).

fof(f36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,
    ( ~ spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f37,f65,f54])).

fof(f37,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f38,f61,f54])).

fof(f38,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f39,f57,f54])).

fof(f39,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (17985)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (17996)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (17987)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (17977)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (17991)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (17977)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f238,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f76,f87,f122,f124,f129,f138,f141,f143,f210,f236])).
% 0.20/0.52  fof(f236,plain,(
% 0.20/0.52    spl3_2 | ~spl3_23),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f224])).
% 0.20/0.52  fof(f224,plain,(
% 0.20/0.52    $false | (spl3_2 | ~spl3_23)),
% 0.20/0.52    inference(subsumption_resolution,[],[f58,f212])).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    k1_xboole_0 = sK2 | ~spl3_23),
% 0.20/0.52    inference(forward_demodulation,[],[f211,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f40,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.52  fof(f211,plain,(
% 0.20/0.52    sK2 = k1_setfam_1(k2_tarski(sK2,k1_xboole_0)) | ~spl3_23),
% 0.20/0.52    inference(resolution,[],[f209,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.20/0.52    inference(definition_unfolding,[],[f46,f45])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.52  fof(f209,plain,(
% 0.20/0.52    r1_tarski(sK2,k1_xboole_0) | ~spl3_23),
% 0.20/0.52    inference(avatar_component_clause,[],[f208])).
% 0.20/0.52  fof(f208,plain,(
% 0.20/0.52    spl3_23 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    k1_xboole_0 != sK2 | spl3_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    spl3_2 <=> k1_xboole_0 = sK2),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.52  fof(f210,plain,(
% 0.20/0.52    ~spl3_4 | ~spl3_3 | spl3_23 | ~spl3_5 | ~spl3_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f205,f85,f69,f208,f61,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    spl3_4 <=> r1_tarski(sK2,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    spl3_3 <=> v3_pre_topc(sK2,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    spl3_7 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.52  fof(f205,plain,(
% 0.20/0.52    r1_tarski(sK2,k1_xboole_0) | ~v3_pre_topc(sK2,sK0) | ~r1_tarski(sK2,sK1) | (~spl3_5 | ~spl3_7)),
% 0.20/0.52    inference(resolution,[],[f188,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f69])).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k1_xboole_0) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1)) ) | ~spl3_7),
% 0.20/0.52    inference(backward_demodulation,[],[f82,f137])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl3_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f85])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1)) )),
% 0.20/0.52    inference(global_subsumption,[],[f33,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f34,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(rectify,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    spl3_7 | ~spl3_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f142,f54,f85])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    spl3_1 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.52    inference(global_subsumption,[],[f33,f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.52    inference(resolution,[],[f34,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    spl3_14),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f139])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    $false | spl3_14),
% 0.20/0.52    inference(subsumption_resolution,[],[f88,f136])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | spl3_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f135])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    spl3_14 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.52    inference(global_subsumption,[],[f33,f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.52    inference(resolution,[],[f34,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    ~spl3_14 | spl3_7 | ~spl3_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f133,f120,f85,f135])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    spl3_13 <=> ! [X0] : (k1_xboole_0 = k1_tops_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X0),sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_13),
% 0.20/0.52    inference(resolution,[],[f121,f34])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1)) ) | ~spl3_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f120])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    spl3_12),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f128])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    $false | spl3_12),
% 0.20/0.52    inference(subsumption_resolution,[],[f33,f118])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    ~l1_pre_topc(sK0) | spl3_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f117])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    spl3_12 <=> l1_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    spl3_11),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f123])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    $false | spl3_11),
% 0.20/0.52    inference(subsumption_resolution,[],[f32,f115])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    ~v2_pre_topc(sK0) | spl3_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f114])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    spl3_11 <=> v2_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    v2_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    ~spl3_11 | ~spl3_12 | spl3_13 | ~spl3_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f112,f74,f120,f117,f114])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    spl3_6 <=> ! [X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k1_tops_1(sK0,X0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl3_6),
% 0.20/0.52    inference(resolution,[],[f111,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    ( ! [X3] : (~v3_pre_topc(X3,sK0) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1)) ) | ~spl3_6),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f110])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ( ! [X3] : (~v3_pre_topc(X3,sK0) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1) | ~r1_tarski(X3,sK1)) ) | ~spl3_6),
% 0.20/0.52    inference(resolution,[],[f103,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(resolution,[],[f34,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.52    inference(nnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | ~v3_pre_topc(X0,sK0) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,X1)) ) | ~spl3_6),
% 0.20/0.52    inference(resolution,[],[f90,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | k1_xboole_0 = X0) ) | ~spl3_6),
% 0.20/0.52    inference(resolution,[],[f75,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f31])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0)) ) | ~spl3_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f74])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    spl3_1 | ~spl3_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f83,f85,f54])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.20/0.52    inference(global_subsumption,[],[f33,f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.52    inference(resolution,[],[f34,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl3_1 | spl3_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f35,f74,f54])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ~spl3_1 | spl3_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f36,f69,f54])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ~spl3_1 | spl3_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f37,f65,f54])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ~spl3_1 | spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f38,f61,f54])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ~spl3_1 | ~spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f39,f57,f54])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (17977)------------------------------
% 0.20/0.52  % (17977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (17977)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (17977)Memory used [KB]: 10874
% 0.20/0.52  % (17977)Time elapsed: 0.100 s
% 0.20/0.52  % (17977)------------------------------
% 0.20/0.52  % (17977)------------------------------
% 0.20/0.52  % (17970)Success in time 0.165 s
%------------------------------------------------------------------------------
