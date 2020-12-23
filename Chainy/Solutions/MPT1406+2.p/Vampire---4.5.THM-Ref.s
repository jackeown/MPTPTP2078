%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1406+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:20 EST 2020

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 119 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  204 ( 482 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4011,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3678,f3683,f3688,f3693,f3698,f3837,f3861,f4010])).

fof(f4010,plain,
    ( ~ spl104_3
    | spl104_4
    | ~ spl104_23
    | ~ spl104_24 ),
    inference(avatar_contradiction_clause,[],[f4009])).

fof(f4009,plain,
    ( $false
    | ~ spl104_3
    | spl104_4
    | ~ spl104_23
    | ~ spl104_24 ),
    inference(subsumption_resolution,[],[f4006,f3864])).

fof(f3864,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl104_4
    | ~ spl104_24 ),
    inference(unit_resulting_resolution,[],[f3687,f3860,f3114])).

fof(f3114,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f2579])).

fof(f2579,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2578])).

fof(f2578,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f3860,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK2))
    | ~ spl104_24 ),
    inference(avatar_component_clause,[],[f3858])).

fof(f3858,plain,
    ( spl104_24
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl104_24])])).

fof(f3687,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl104_4 ),
    inference(avatar_component_clause,[],[f3685])).

fof(f3685,plain,
    ( spl104_4
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl104_4])])).

fof(f4006,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl104_3
    | ~ spl104_23 ),
    inference(unit_resulting_resolution,[],[f3682,f3836,f3180])).

fof(f3180,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2636])).

fof(f2636,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2159])).

fof(f2159,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f3836,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl104_23 ),
    inference(avatar_component_clause,[],[f3834])).

fof(f3834,plain,
    ( spl104_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl104_23])])).

fof(f3682,plain,
    ( l1_pre_topc(sK0)
    | ~ spl104_3 ),
    inference(avatar_component_clause,[],[f3680])).

fof(f3680,plain,
    ( spl104_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl104_3])])).

fof(f3861,plain,
    ( spl104_24
    | ~ spl104_2
    | ~ spl104_3
    | ~ spl104_5
    | ~ spl104_6 ),
    inference(avatar_split_clause,[],[f3768,f3695,f3690,f3680,f3675,f3858])).

fof(f3675,plain,
    ( spl104_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl104_2])])).

fof(f3690,plain,
    ( spl104_5
  <=> m2_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl104_5])])).

fof(f3695,plain,
    ( spl104_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl104_6])])).

fof(f3768,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK2))
    | ~ spl104_2
    | ~ spl104_3
    | ~ spl104_5
    | ~ spl104_6 ),
    inference(unit_resulting_resolution,[],[f3677,f3682,f3692,f3697,f3628])).

fof(f3628,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f3136,f3135])).

fof(f3135,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f2590])).

fof(f2590,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2589])).

fof(f2589,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2530])).

fof(f2530,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(f3136,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2924])).

fof(f2924,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2592])).

fof(f2592,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2591])).

fof(f2591,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2518])).

fof(f2518,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f3697,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl104_6 ),
    inference(avatar_component_clause,[],[f3695])).

fof(f3692,plain,
    ( m2_connsp_2(sK2,sK0,sK1)
    | ~ spl104_5 ),
    inference(avatar_component_clause,[],[f3690])).

fof(f3677,plain,
    ( v2_pre_topc(sK0)
    | ~ spl104_2 ),
    inference(avatar_component_clause,[],[f3675])).

fof(f3837,plain,
    ( spl104_23
    | ~ spl104_2
    | ~ spl104_3
    | ~ spl104_5
    | ~ spl104_6 ),
    inference(avatar_split_clause,[],[f3767,f3695,f3690,f3680,f3675,f3834])).

fof(f3767,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl104_2
    | ~ spl104_3
    | ~ spl104_5
    | ~ spl104_6 ),
    inference(unit_resulting_resolution,[],[f3677,f3682,f3692,f3697,f3135])).

fof(f3698,plain,(
    spl104_6 ),
    inference(avatar_split_clause,[],[f3111,f3695])).

fof(f3111,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2906])).

fof(f2906,plain,
    ( ~ r1_tarski(sK1,sK2)
    & m2_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2577,f2905,f2904,f2903])).

fof(f2903,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X1,X2)
                & m2_connsp_2(X2,X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,sK0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2904,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & m2_connsp_2(X2,sK0,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK1,X2)
          & m2_connsp_2(X2,sK0,sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2905,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK1,X2)
        & m2_connsp_2(X2,sK0,sK1) )
   => ( ~ r1_tarski(sK1,sK2)
      & m2_connsp_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2577,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2576])).

fof(f2576,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2560])).

fof(f2560,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_connsp_2(X2,X0,X1)
               => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f2559])).

fof(f2559,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_connsp_2(X2,X0,X1)
             => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_connsp_2)).

fof(f3693,plain,(
    spl104_5 ),
    inference(avatar_split_clause,[],[f3112,f3690])).

fof(f3112,plain,(
    m2_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f2906])).

fof(f3688,plain,(
    ~ spl104_4 ),
    inference(avatar_split_clause,[],[f3113,f3685])).

fof(f3113,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f2906])).

fof(f3683,plain,(
    spl104_3 ),
    inference(avatar_split_clause,[],[f3110,f3680])).

fof(f3110,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2906])).

fof(f3678,plain,(
    spl104_2 ),
    inference(avatar_split_clause,[],[f3109,f3675])).

fof(f3109,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2906])).
%------------------------------------------------------------------------------
