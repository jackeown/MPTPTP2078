%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1859+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:35 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 241 expanded)
%              Number of leaves         :    5 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  247 (1607 expanded)
%              Number of equality atoms :   19 ( 220 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6213,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6181,f6176])).

fof(f6176,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f6175,f4369])).

fof(f4369,plain,
    ( v1_tdlat_3(sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(literal_reordering,[],[f4010])).

fof(f4010,plain,
    ( v1_tdlat_3(sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f3874])).

fof(f3874,plain,
    ( ( ~ v1_tdlat_3(sK2)
      | ~ v2_tex_2(sK3,sK2) )
    & ( v1_tdlat_3(sK2)
      | v2_tex_2(sK3,sK2) )
    & u1_struct_0(sK2) = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f3871,f3873,f3872])).

fof(f3872,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_tdlat_3(X0)
              | v2_tex_2(X1,X0) )
            & u1_struct_0(X0) = X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_tdlat_3(sK2)
            | ~ v2_tex_2(X1,sK2) )
          & ( v1_tdlat_3(sK2)
            | v2_tex_2(X1,sK2) )
          & u1_struct_0(sK2) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3873,plain,
    ( ? [X1] :
        ( ( ~ v1_tdlat_3(sK2)
          | ~ v2_tex_2(X1,sK2) )
        & ( v1_tdlat_3(sK2)
          | v2_tex_2(X1,sK2) )
        & u1_struct_0(sK2) = X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ~ v1_tdlat_3(sK2)
        | ~ v2_tex_2(sK3,sK2) )
      & ( v1_tdlat_3(sK2)
        | v2_tex_2(sK3,sK2) )
      & u1_struct_0(sK2) = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f3871,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tdlat_3(X0)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_tdlat_3(X0)
            | v2_tex_2(X1,X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3870])).

fof(f3870,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_tdlat_3(X0)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_tdlat_3(X0)
            | v2_tex_2(X1,X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3677])).

fof(f3677,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3676])).

fof(f3676,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3661])).

fof(f3661,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( u1_struct_0(X0) = X1
             => ( v2_tex_2(X1,X0)
              <=> v1_tdlat_3(X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f3660])).

fof(f3660,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

fof(f6175,plain,
    ( ~ v1_tdlat_3(sK2)
    | v2_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f6174,f4373])).

fof(f4373,plain,(
    ~ v2_struct_0(sK2) ),
    inference(literal_reordering,[],[f4006])).

fof(f4006,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3874])).

fof(f6174,plain,
    ( ~ v1_tdlat_3(sK2)
    | v2_tex_2(sK3,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f6173,f5407])).

fof(f5407,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(resolution,[],[f4372,f4548])).

fof(f4548,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(literal_reordering,[],[f4186])).

fof(f4186,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3781])).

fof(f3781,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3456])).

fof(f3456,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f4372,plain,(
    l1_pre_topc(sK2) ),
    inference(literal_reordering,[],[f4007])).

fof(f4007,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f3874])).

fof(f6173,plain,
    ( ~ v1_tdlat_3(sK2)
    | v2_tex_2(sK3,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f6172,f5553])).

fof(f5553,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK3)) ),
    inference(forward_demodulation,[],[f4371,f4370])).

fof(f4370,plain,(
    u1_struct_0(sK2) = sK3 ),
    inference(literal_reordering,[],[f4009])).

fof(f4009,plain,(
    u1_struct_0(sK2) = sK3 ),
    inference(cnf_transformation,[],[f3874])).

fof(f4371,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(literal_reordering,[],[f4008])).

fof(f4008,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f3874])).

fof(f6172,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ v1_tdlat_3(sK2)
    | v2_tex_2(sK3,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f5489,f4370])).

fof(f5489,plain,(
    ! [X3] :
      ( ~ m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(sK3))
      | ~ v1_tdlat_3(X3)
      | v2_tex_2(u1_struct_0(X3),sK2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f5488,f4373])).

fof(f5488,plain,(
    ! [X3] :
      ( ~ m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(sK3))
      | ~ v1_tdlat_3(X3)
      | v2_tex_2(u1_struct_0(X3),sK2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5421,f4372])).

fof(f5421,plain,(
    ! [X3] :
      ( ~ m1_subset_1(u1_struct_0(X3),k1_zfmisc_1(sK3))
      | ~ v1_tdlat_3(X3)
      | v2_tex_2(u1_struct_0(X3),sK2)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f4437,f4370])).

fof(f4437,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4336])).

fof(f4336,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4076])).

fof(f4076,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3889])).

fof(f3889,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3711])).

fof(f3711,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3710])).

fof(f3710,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3659])).

fof(f3659,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f6181,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f6180,f4368])).

fof(f4368,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ v1_tdlat_3(sK2) ),
    inference(literal_reordering,[],[f4011])).

fof(f4011,plain,
    ( ~ v1_tdlat_3(sK2)
    | ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f3874])).

fof(f6180,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v1_tdlat_3(sK2) ),
    inference(subsumption_resolution,[],[f6179,f4373])).

fof(f6179,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v1_tdlat_3(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f6178,f5407])).

fof(f6178,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | v1_tdlat_3(sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f6177,f5553])).

fof(f6177,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK3))
    | ~ v2_tex_2(sK3,sK2)
    | v1_tdlat_3(sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f5492,f4370])).

fof(f5492,plain,(
    ! [X5] :
      ( ~ m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(sK3))
      | ~ v2_tex_2(u1_struct_0(X5),sK2)
      | v1_tdlat_3(X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5) ) ),
    inference(subsumption_resolution,[],[f5491,f4373])).

fof(f5491,plain,(
    ! [X5] :
      ( ~ m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(sK3))
      | ~ v2_tex_2(u1_struct_0(X5),sK2)
      | v1_tdlat_3(X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f5423,f4372])).

fof(f5423,plain,(
    ! [X5] :
      ( ~ m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(sK3))
      | ~ v2_tex_2(u1_struct_0(X5),sK2)
      | v1_tdlat_3(X5)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f4438,f4370])).

fof(f4438,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(literal_reordering,[],[f4337])).

fof(f4337,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4075])).

fof(f4075,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3889])).
%------------------------------------------------------------------------------
