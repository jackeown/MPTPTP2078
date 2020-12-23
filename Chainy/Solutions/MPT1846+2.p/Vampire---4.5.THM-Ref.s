%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1846+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:34 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 350 expanded)
%              Number of leaves         :    6 ( 110 expanded)
%              Depth                    :   21
%              Number of atoms          :  207 (2668 expanded)
%              Number of equality atoms :   31 ( 395 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4657,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4656,f4444])).

fof(f4444,plain,(
    v1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f4443,f3886])).

fof(f3886,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f3775])).

fof(f3775,plain,
    ( ( ~ v1_tex_2(sK3,sK2)
      | ~ v1_subset_1(sK4,u1_struct_0(sK2)) )
    & ( v1_tex_2(sK3,sK2)
      | v1_subset_1(sK4,u1_struct_0(sK2)) )
    & u1_struct_0(sK3) = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_pre_topc(sK3,sK2)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f3771,f3774,f3773,f3772])).

fof(f3772,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) )
                & ( v1_tex_2(X1,X0)
                  | v1_subset_1(X2,u1_struct_0(X0)) )
                & u1_struct_0(X1) = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,sK2)
                | ~ v1_subset_1(X2,u1_struct_0(sK2)) )
              & ( v1_tex_2(X1,sK2)
                | v1_subset_1(X2,u1_struct_0(sK2)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_pre_topc(X1,sK2) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3773,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ v1_tex_2(X1,sK2)
              | ~ v1_subset_1(X2,u1_struct_0(sK2)) )
            & ( v1_tex_2(X1,sK2)
              | v1_subset_1(X2,u1_struct_0(sK2)) )
            & u1_struct_0(X1) = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_pre_topc(X1,sK2) )
   => ( ? [X2] :
          ( ( ~ v1_tex_2(sK3,sK2)
            | ~ v1_subset_1(X2,u1_struct_0(sK2)) )
          & ( v1_tex_2(sK3,sK2)
            | v1_subset_1(X2,u1_struct_0(sK2)) )
          & u1_struct_0(sK3) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_pre_topc(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3774,plain,
    ( ? [X2] :
        ( ( ~ v1_tex_2(sK3,sK2)
          | ~ v1_subset_1(X2,u1_struct_0(sK2)) )
        & ( v1_tex_2(sK3,sK2)
          | v1_subset_1(X2,u1_struct_0(sK2)) )
        & u1_struct_0(sK3) = X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ~ v1_tex_2(sK3,sK2)
        | ~ v1_subset_1(sK4,u1_struct_0(sK2)) )
      & ( v1_tex_2(sK3,sK2)
        | v1_subset_1(sK4,u1_struct_0(sK2)) )
      & u1_struct_0(sK3) = sK4
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f3771,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3770])).

fof(f3770,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v1_tex_2(X1,X0)
                | ~ v1_subset_1(X2,u1_struct_0(X0)) )
              & ( v1_tex_2(X1,X0)
                | v1_subset_1(X2,u1_struct_0(X0)) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3617])).

fof(f3617,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <~> v1_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3616])).

fof(f3616,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <~> v1_tex_2(X1,X0) )
              & u1_struct_0(X1) = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3595])).

fof(f3595,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => ( v1_subset_1(X2,u1_struct_0(X0))
                  <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3594])).

fof(f3594,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

fof(f4443,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f4442,f3887])).

fof(f3887,plain,(
    u1_struct_0(sK3) = sK4 ),
    inference(cnf_transformation,[],[f3775])).

fof(f4442,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(duplicate_literal_removal,[],[f4441])).

fof(f4441,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK2))
    | v1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f4440,f3887])).

fof(f4440,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f4439,f3884])).

fof(f3884,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f3775])).

fof(f4439,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f4438,f3885])).

fof(f3885,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f3775])).

fof(f4438,plain,
    ( v1_subset_1(sK4,u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f3888,f4105])).

fof(f4105,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f3890])).

fof(f3890,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3779])).

fof(f3779,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK5(X0,X1)
                & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f3777,f3778])).

fof(f3778,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK5(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK5(X0,X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3777,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f3776])).

fof(f3776,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3619])).

fof(f3619,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3618])).

fof(f3618,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3567])).

fof(f3567,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f3888,plain,
    ( v1_tex_2(sK3,sK2)
    | v1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f3775])).

fof(f4656,plain,(
    ~ v1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f4544,f4542])).

fof(f4542,plain,(
    sK4 = sK5(sK2,sK3) ),
    inference(forward_demodulation,[],[f4541,f3887])).

fof(f4541,plain,(
    u1_struct_0(sK3) = sK5(sK2,sK3) ),
    inference(subsumption_resolution,[],[f4540,f3884])).

fof(f4540,plain,
    ( u1_struct_0(sK3) = sK5(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f4536,f3885])).

fof(f4536,plain,
    ( u1_struct_0(sK3) = sK5(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f4533,f3892])).

fof(f3892,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK5(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3779])).

fof(f4533,plain,(
    ~ v1_tex_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f3889,f4444])).

fof(f3889,plain,
    ( ~ v1_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f3775])).

fof(f4544,plain,(
    ~ v1_subset_1(sK5(sK2,sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f4543,f3884])).

fof(f4543,plain,
    ( ~ v1_subset_1(sK5(sK2,sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f4537,f3885])).

fof(f4537,plain,
    ( ~ v1_subset_1(sK5(sK2,sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f4533,f3893])).

fof(f3893,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3779])).
%------------------------------------------------------------------------------
