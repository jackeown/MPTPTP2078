%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1881+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:36 EST 2020

% Result     : Theorem 26.90s
% Output     : Refutation 27.29s
% Verified   : 
% Statistics : Number of formulae       :  176 (1696 expanded)
%              Number of leaves         :   25 ( 452 expanded)
%              Depth                    :   23
%              Number of atoms          :  691 (11855 expanded)
%              Number of equality atoms :   38 ( 142 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48251,plain,(
    $false ),
    inference(global_subsumption,[],[f8417,f12086,f42253,f48249,f48250])).

fof(f48250,plain,(
    u1_struct_0(sK74) != sK75 ),
    inference(subsumption_resolution,[],[f47809,f48249])).

fof(f47809,plain,
    ( u1_struct_0(sK74) != sK75
    | v1_tops_1(sK75,sK74) ),
    inference(backward_demodulation,[],[f8608,f47775])).

fof(f47775,plain,(
    sK75 = k2_pre_topc(sK74,sK75) ),
    inference(resolution,[],[f47289,f8831])).

fof(f8831,plain,
    ( ~ v4_pre_topc(sK75,sK74)
    | sK75 = k2_pre_topc(sK74,sK75) ),
    inference(subsumption_resolution,[],[f8335,f5360])).

fof(f5360,plain,(
    l1_pre_topc(sK74) ),
    inference(cnf_transformation,[],[f4709])).

fof(f4709,plain,
    ( ( v1_subset_1(sK75,u1_struct_0(sK74))
      | ~ v3_tex_2(sK75,sK74) )
    & ( ~ v1_subset_1(sK75,u1_struct_0(sK74))
      | v3_tex_2(sK75,sK74) )
    & m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74)))
    & l1_pre_topc(sK74)
    & v1_tdlat_3(sK74)
    & v2_pre_topc(sK74)
    & ~ v2_struct_0(sK74) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK74,sK75])],[f4706,f4708,f4707])).

fof(f4707,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK74))
            | ~ v3_tex_2(X1,sK74) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK74))
            | v3_tex_2(X1,sK74) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK74))) )
      & l1_pre_topc(sK74)
      & v1_tdlat_3(sK74)
      & v2_pre_topc(sK74)
      & ~ v2_struct_0(sK74) ) ),
    introduced(choice_axiom,[])).

fof(f4708,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK74))
          | ~ v3_tex_2(X1,sK74) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK74))
          | v3_tex_2(X1,sK74) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK74))) )
   => ( ( v1_subset_1(sK75,u1_struct_0(sK74))
        | ~ v3_tex_2(sK75,sK74) )
      & ( ~ v1_subset_1(sK75,u1_struct_0(sK74))
        | v3_tex_2(sK75,sK74) )
      & m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74))) ) ),
    introduced(choice_axiom,[])).

fof(f4706,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4705])).

fof(f4705,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3722])).

fof(f3722,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3721])).

fof(f3721,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3700])).

fof(f3700,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3699])).

fof(f3699,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f8335,plain,
    ( sK75 = k2_pre_topc(sK74,sK75)
    | ~ v4_pre_topc(sK75,sK74)
    | ~ l1_pre_topc(sK74) ),
    inference(resolution,[],[f5361,f6491])).

fof(f6491,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4441])).

fof(f4441,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f4440])).

fof(f4440,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1843])).

fof(f1843,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f5361,plain,(
    m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74))) ),
    inference(cnf_transformation,[],[f4709])).

fof(f47289,plain,(
    v4_pre_topc(sK75,sK74) ),
    inference(forward_demodulation,[],[f47288,f9001])).

fof(f9001,plain,(
    sK75 = k3_subset_1(u1_struct_0(sK74),k4_xboole_0(u1_struct_0(sK74),sK75)) ),
    inference(backward_demodulation,[],[f8472,f8473])).

fof(f8473,plain,(
    k3_subset_1(u1_struct_0(sK74),sK75) = k4_xboole_0(u1_struct_0(sK74),sK75) ),
    inference(resolution,[],[f5361,f5470])).

fof(f5470,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3821])).

fof(f3821,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f8472,plain,(
    sK75 = k3_subset_1(u1_struct_0(sK74),k3_subset_1(u1_struct_0(sK74),sK75)) ),
    inference(resolution,[],[f5361,f5469])).

fof(f5469,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3820])).

fof(f3820,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f47288,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0(sK74),k4_xboole_0(u1_struct_0(sK74),sK75)),sK74) ),
    inference(subsumption_resolution,[],[f47287,f5358])).

fof(f5358,plain,(
    v2_pre_topc(sK74) ),
    inference(cnf_transformation,[],[f4709])).

fof(f47287,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK74),k4_xboole_0(u1_struct_0(sK74),sK75)),sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f47286,f5360])).

fof(f47286,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK74),k4_xboole_0(u1_struct_0(sK74),sK75)),sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f46878,f47285])).

fof(f47285,plain,(
    v3_pre_topc(k4_xboole_0(u1_struct_0(sK74),sK75),sK74) ),
    inference(subsumption_resolution,[],[f47284,f5358])).

fof(f47284,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f47283,f5360])).

fof(f47283,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f46877,f5359])).

fof(f5359,plain,(
    v1_tdlat_3(sK74) ),
    inference(cnf_transformation,[],[f4709])).

fof(f46877,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v1_tdlat_3(sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(resolution,[],[f9013,f5430])).

fof(f5430,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4738])).

fof(f4738,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK86(X0),X0)
            & m1_subset_1(sK86(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK86])],[f4736,f4737])).

fof(f4737,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK86(X0),X0)
        & m1_subset_1(sK86(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4736,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f4735])).

fof(f4735,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3780])).

fof(f3780,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3779])).

fof(f3779,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3662])).

fof(f3662,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f9013,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK74),sK75),k1_zfmisc_1(u1_struct_0(sK74))) ),
    inference(forward_demodulation,[],[f8474,f8473])).

fof(f8474,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK74),sK75),k1_zfmisc_1(u1_struct_0(sK74))) ),
    inference(resolution,[],[f5361,f5471])).

fof(f5471,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f3822])).

fof(f3822,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f46878,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK74),k4_xboole_0(u1_struct_0(sK74),sK75)),sK74)
    | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(resolution,[],[f9013,f5445])).

fof(f5445,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3796])).

fof(f3796,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3795])).

fof(f3795,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2113])).

fof(f2113,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_tops_1)).

fof(f8608,plain,
    ( v1_tops_1(sK75,sK74)
    | u1_struct_0(sK74) != k2_pre_topc(sK74,sK75) ),
    inference(subsumption_resolution,[],[f8197,f5360])).

fof(f8197,plain,
    ( v1_tops_1(sK75,sK74)
    | u1_struct_0(sK74) != k2_pre_topc(sK74,sK75)
    | ~ l1_pre_topc(sK74) ),
    inference(resolution,[],[f5361,f5635])).

fof(f5635,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4841])).

fof(f4841,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3925])).

fof(f3925,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3602])).

fof(f3602,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f48249,plain,(
    ~ v1_tops_1(sK75,sK74) ),
    inference(global_subsumption,[],[f47336,f47571])).

fof(f47571,plain,(
    ~ v2_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74) ),
    inference(global_subsumption,[],[f38869,f47507])).

fof(f47507,plain,(
    ~ v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74) ),
    inference(global_subsumption,[],[f9010,f9065,f47316,f47506])).

fof(f47506,plain,
    ( v1_xboole_0(k4_xboole_0(u1_struct_0(sK74),sK75))
    | ~ v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74) ),
    inference(subsumption_resolution,[],[f47505,f5358])).

fof(f47505,plain,
    ( v1_xboole_0(k4_xboole_0(u1_struct_0(sK74),sK75))
    | ~ v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f47504,f5360])).

fof(f47504,plain,
    ( v1_xboole_0(k4_xboole_0(u1_struct_0(sK74),sK75))
    | ~ v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f47010,f47285])).

fof(f47010,plain,
    ( v1_xboole_0(k4_xboole_0(u1_struct_0(sK74),sK75))
    | ~ v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(resolution,[],[f9013,f6438])).

fof(f6438,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v3_tops_1(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4404])).

fof(f4404,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v3_tops_1(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f4403])).

fof(f4403,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v3_tops_1(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2091])).

fof(f2091,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tops_1)).

fof(f47316,plain,
    ( v1_tops_1(sK75,sK74)
    | ~ v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74) ),
    inference(forward_demodulation,[],[f47315,f9001])).

fof(f47315,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK74),k4_xboole_0(u1_struct_0(sK74),sK75)),sK74)
    | ~ v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74) ),
    inference(subsumption_resolution,[],[f47314,f5358])).

fof(f47314,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK74),k4_xboole_0(u1_struct_0(sK74),sK75)),sK74)
    | ~ v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f46894,f5360])).

fof(f46894,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK74),k4_xboole_0(u1_struct_0(sK74),sK75)),sK74)
    | ~ v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(resolution,[],[f9013,f5618])).

fof(f5618,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3914])).

fof(f3914,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3913])).

fof(f3913,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2108])).

fof(f2108,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_tops_1(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc15_tops_1)).

fof(f9065,plain,
    ( ~ v1_tops_1(sK75,sK74)
    | v1_subset_1(sK75,u1_struct_0(sK74)) ),
    inference(subsumption_resolution,[],[f9064,f5357])).

fof(f5357,plain,(
    ~ v2_struct_0(sK74) ),
    inference(cnf_transformation,[],[f4709])).

fof(f9064,plain,
    ( v1_subset_1(sK75,u1_struct_0(sK74))
    | ~ v1_tops_1(sK75,sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f9063,f5358])).

fof(f9063,plain,
    ( v1_subset_1(sK75,u1_struct_0(sK74))
    | ~ v1_tops_1(sK75,sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f9062,f5360])).

fof(f9062,plain,
    ( v1_subset_1(sK75,u1_struct_0(sK74))
    | ~ v1_tops_1(sK75,sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f9061,f5361])).

fof(f9061,plain,
    ( v1_subset_1(sK75,u1_struct_0(sK74))
    | ~ v1_tops_1(sK75,sK74)
    | ~ m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74)))
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f9057,f8672])).

fof(f8672,plain,(
    v2_tex_2(sK75,sK74) ),
    inference(subsumption_resolution,[],[f8671,f5357])).

fof(f8671,plain,
    ( v2_tex_2(sK75,sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f8670,f5358])).

fof(f8670,plain,
    ( v2_tex_2(sK75,sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f8669,f5359])).

fof(f8669,plain,
    ( v2_tex_2(sK75,sK74)
    | ~ v1_tdlat_3(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f8222,f5360])).

fof(f8222,plain,
    ( v2_tex_2(sK75,sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v1_tdlat_3(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f5361,f5680])).

fof(f5680,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3963])).

fof(f3963,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3962])).

fof(f3962,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3693])).

fof(f3693,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f9057,plain,
    ( v1_subset_1(sK75,u1_struct_0(sK74))
    | ~ v2_tex_2(sK75,sK74)
    | ~ v1_tops_1(sK75,sK74)
    | ~ m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74)))
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f5363,f5417])).

fof(f5417,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3774])).

fof(f3774,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3773])).

fof(f3773,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3698])).

fof(f3698,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f5363,plain,
    ( ~ v3_tex_2(sK75,sK74)
    | v1_subset_1(sK75,u1_struct_0(sK74)) ),
    inference(cnf_transformation,[],[f4709])).

fof(f9010,plain,
    ( ~ v1_xboole_0(k4_xboole_0(u1_struct_0(sK74),sK75))
    | ~ v1_subset_1(sK75,u1_struct_0(sK74)) ),
    inference(backward_demodulation,[],[f8967,f8473])).

fof(f8967,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK74),sK75))
    | ~ v1_subset_1(sK75,u1_struct_0(sK74)) ),
    inference(global_subsumption,[],[f6943,f7775,f8416])).

fof(f8416,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK74),sK75))
    | ~ v1_subset_1(sK75,u1_struct_0(sK74))
    | v1_xboole_0(u1_struct_0(sK74)) ),
    inference(resolution,[],[f5361,f5364])).

fof(f5364,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3724])).

fof(f3724,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3723])).

fof(f3723,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3613])).

fof(f3613,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & v1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

fof(f7775,plain,(
    l1_struct_0(sK74) ),
    inference(resolution,[],[f5360,f5542])).

fof(f5542,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3878])).

fof(f3878,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f6943,plain,
    ( ~ l1_struct_0(sK74)
    | ~ v1_xboole_0(u1_struct_0(sK74)) ),
    inference(resolution,[],[f5357,f5541])).

fof(f5541,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3877])).

fof(f3877,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3876])).

fof(f3876,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f38869,plain,
    ( v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v2_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74) ),
    inference(subsumption_resolution,[],[f38868,f5358])).

fof(f38868,plain,
    ( v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v2_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f38867,f5360])).

fof(f38867,plain,
    ( v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v2_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f38779,f9013])).

fof(f38779,plain,
    ( v3_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v2_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK74),sK75),k1_zfmisc_1(u1_struct_0(sK74)))
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(resolution,[],[f9002,f6506])).

fof(f6506,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4453])).

fof(f4453,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f4452])).

fof(f4452,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2090])).

fof(f2090,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tops_1(X1,X0)
              & v4_pre_topc(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tops_1)).

fof(f9002,plain,(
    v4_pre_topc(k4_xboole_0(u1_struct_0(sK74),sK75),sK74) ),
    inference(backward_demodulation,[],[f8576,f8473])).

fof(f8576,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0(sK74),sK75),sK74) ),
    inference(subsumption_resolution,[],[f8575,f5358])).

fof(f8575,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK74),sK75),sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f8574,f5360])).

fof(f8574,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK74),sK75),sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f8169,f8573])).

fof(f8573,plain,(
    v3_pre_topc(sK75,sK74) ),
    inference(subsumption_resolution,[],[f8572,f5358])).

fof(f8572,plain,
    ( v3_pre_topc(sK75,sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f8571,f5360])).

fof(f8571,plain,
    ( v3_pre_topc(sK75,sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f8168,f5359])).

fof(f8168,plain,
    ( v3_pre_topc(sK75,sK74)
    | ~ v1_tdlat_3(sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(resolution,[],[f5361,f5430])).

fof(f8169,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK74),sK75),sK74)
    | ~ v3_pre_topc(sK75,sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(resolution,[],[f5361,f5445])).

fof(f47336,plain,
    ( ~ v1_tops_1(sK75,sK74)
    | v2_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74) ),
    inference(forward_demodulation,[],[f47335,f9001])).

fof(f47335,plain,
    ( v2_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK74),k4_xboole_0(u1_struct_0(sK74),sK75)),sK74) ),
    inference(subsumption_resolution,[],[f46908,f5360])).

fof(f46908,plain,
    ( v2_tops_1(k4_xboole_0(u1_struct_0(sK74),sK75),sK74)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK74),k4_xboole_0(u1_struct_0(sK74),sK75)),sK74)
    | ~ l1_pre_topc(sK74) ),
    inference(resolution,[],[f9013,f5637])).

fof(f5637,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4842])).

fof(f4842,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3926])).

fof(f3926,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2095])).

fof(f2095,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f42253,plain,
    ( ~ v1_subset_1(sK75,u1_struct_0(sK74))
    | sP4(sK75,sK74) ),
    inference(subsumption_resolution,[],[f42239,f8596])).

fof(f8596,plain,(
    sP5(sK74,sK75) ),
    inference(subsumption_resolution,[],[f8595,f5358])).

fof(f8595,plain,
    ( sP5(sK74,sK75)
    | ~ v2_pre_topc(sK74) ),
    inference(subsumption_resolution,[],[f8189,f5360])).

fof(f8189,plain,
    ( sP5(sK74,sK75)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74) ),
    inference(resolution,[],[f5361,f5627])).

fof(f5627,plain,(
    ! [X0,X1] :
      ( sP5(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4597])).

fof(f4597,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP5(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f3918,f4596,f4595])).

fof(f4595,plain,(
    ! [X1,X0] :
      ( sP4(X1,X0)
    <=> ! [X2] :
          ( ~ r1_xboole_0(X1,X2)
          | ~ v3_pre_topc(X2,X0)
          | k1_xboole_0 = X2
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f4596,plain,(
    ! [X0,X1] :
      ( ( v1_tops_1(X1,X0)
      <=> sP4(X1,X0) )
      | ~ sP5(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f3918,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3917])).

fof(f3917,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2188])).

fof(f2188,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).

fof(f42239,plain,
    ( ~ v1_subset_1(sK75,u1_struct_0(sK74))
    | sP4(sK75,sK74)
    | ~ sP5(sK74,sK75) ),
    inference(resolution,[],[f9046,f5620])).

fof(f5620,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f4833])).

fof(f4833,plain,(
    ! [X0,X1] :
      ( ( ( v1_tops_1(X1,X0)
          | ~ sP4(X1,X0) )
        & ( sP4(X1,X0)
          | ~ v1_tops_1(X1,X0) ) )
      | ~ sP5(X0,X1) ) ),
    inference(nnf_transformation,[],[f4596])).

fof(f9046,plain,
    ( v1_tops_1(sK75,sK74)
    | ~ v1_subset_1(sK75,u1_struct_0(sK74)) ),
    inference(subsumption_resolution,[],[f9045,f5357])).

fof(f9045,plain,
    ( ~ v1_subset_1(sK75,u1_struct_0(sK74))
    | v1_tops_1(sK75,sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f9044,f5358])).

fof(f9044,plain,
    ( ~ v1_subset_1(sK75,u1_struct_0(sK74))
    | v1_tops_1(sK75,sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f9043,f5360])).

fof(f9043,plain,
    ( ~ v1_subset_1(sK75,u1_struct_0(sK74))
    | v1_tops_1(sK75,sK74)
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f9042,f5361])).

fof(f9042,plain,
    ( ~ v1_subset_1(sK75,u1_struct_0(sK74))
    | v1_tops_1(sK75,sK74)
    | ~ m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74)))
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(subsumption_resolution,[],[f9037,f8573])).

fof(f9037,plain,
    ( ~ v1_subset_1(sK75,u1_struct_0(sK74))
    | v1_tops_1(sK75,sK74)
    | ~ v3_pre_topc(sK75,sK74)
    | ~ m1_subset_1(sK75,k1_zfmisc_1(u1_struct_0(sK74)))
    | ~ l1_pre_topc(sK74)
    | ~ v2_pre_topc(sK74)
    | v2_struct_0(sK74) ),
    inference(resolution,[],[f5362,f5416])).

fof(f5416,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3772])).

fof(f3772,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3771])).

fof(f3771,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3697])).

fof(f3697,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f5362,plain,
    ( v3_tex_2(sK75,sK74)
    | ~ v1_subset_1(sK75,u1_struct_0(sK74)) ),
    inference(cnf_transformation,[],[f4709])).

fof(f12086,plain,
    ( v1_tops_1(sK75,sK74)
    | ~ sP4(sK75,sK74) ),
    inference(resolution,[],[f8596,f5621])).

fof(f5621,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ sP4(X1,X0)
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f4833])).

fof(f8417,plain,
    ( v1_subset_1(sK75,u1_struct_0(sK74))
    | u1_struct_0(sK74) = sK75 ),
    inference(resolution,[],[f5361,f5366])).

fof(f5366,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f4710])).

fof(f4710,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f3725])).

fof(f3725,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3609])).

fof(f3609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
%------------------------------------------------------------------------------
