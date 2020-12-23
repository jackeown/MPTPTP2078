%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 (1268 expanded)
%              Number of leaves         :   15 ( 332 expanded)
%              Depth                    :   28
%              Number of atoms          :  479 (9158 expanded)
%              Number of equality atoms :   57 ( 205 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f463,plain,(
    $false ),
    inference(subsumption_resolution,[],[f462,f453])).

fof(f453,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(forward_demodulation,[],[f452,f405])).

fof(f405,plain,(
    u1_struct_0(sK0) = sK1 ),
    inference(subsumption_resolution,[],[f394,f340])).

fof(f340,plain,
    ( v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = sK1 ),
    inference(subsumption_resolution,[],[f339,f51])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
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
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(f339,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = sK1 ),
    inference(subsumption_resolution,[],[f335,f52])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f335,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = sK1 ),
    inference(trivial_inequality_removal,[],[f331])).

fof(f331,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = sK1 ),
    inference(superposition,[],[f61,f288])).

fof(f288,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f174,f124])).

fof(f124,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1 ),
    inference(resolution,[],[f52,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f174,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f173,f51])).

fof(f173,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f172,f52])).

fof(f172,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f155,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f155,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f154,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f154,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v1_tops_1(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f153,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f153,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v1_tops_1(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f152,f51])).

fof(f152,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f151,f52])).

fof(f151,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f150,f146])).

fof(f146,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f145,f49])).

fof(f145,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f144,f51])).

fof(f144,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f122,f50])).

fof(f50,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f122,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f52,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK2(X0),X0)
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f150,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v1_tops_1(sK1,sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f53,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f394,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ v1_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f129,f392])).

fof(f392,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f391,f70])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f391,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f326,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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

fof(f326,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f196,f96])).

fof(f96,plain,(
    ! [X4] :
      ( v3_pre_topc(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f95,f51])).

fof(f95,plain,(
    ! [X4] :
      ( v3_pre_topc(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f91,f50])).

fof(f91,plain,(
    ! [X4] :
      ( v3_pre_topc(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f49,f67])).

fof(f196,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f195,f125])).

fof(f125,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f52,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f195,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f194,f51])).

fof(f194,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f192,f52])).

fof(f192,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f126,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f126,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f113,f51])).

fof(f113,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f129,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f115,f51])).

fof(f115,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f60])).

fof(f452,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f400,f405])).

fof(f400,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f234,f392])).

fof(f234,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f216,f54])).

fof(f54,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f216,plain,
    ( v3_tex_2(sK1,sK0)
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f215,f48])).

fof(f215,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | v3_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f214,f49])).

fof(f214,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | v3_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f213,f51])).

fof(f213,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f212,f52])).

fof(f212,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | v3_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f210,f136])).

fof(f136,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f135,f48])).

fof(f135,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f134,f49])).

fof(f134,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f133,f50])).

fof(f133,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f119,f51])).

fof(f119,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f52,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f210,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f130,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f130,plain,
    ( v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f116,f51])).

fof(f116,plain,
    ( v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f61])).

fof(f462,plain,(
    ~ v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f406,f76])).

fof(f76,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f406,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f52,f405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:20:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.41  % (29113)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.41  % (29117)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.41  % (29113)Refutation not found, incomplete strategy% (29113)------------------------------
% 0.20/0.41  % (29113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (29113)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (29113)Memory used [KB]: 6140
% 0.20/0.41  % (29113)Time elapsed: 0.036 s
% 0.20/0.41  % (29113)------------------------------
% 0.20/0.41  % (29113)------------------------------
% 0.20/0.42  % (29117)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % (29129)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f463,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f462,f453])).
% 0.20/0.42  fof(f453,plain,(
% 0.20/0.42    v1_subset_1(sK1,sK1)),
% 0.20/0.42    inference(forward_demodulation,[],[f452,f405])).
% 0.20/0.42  fof(f405,plain,(
% 0.20/0.42    u1_struct_0(sK0) = sK1),
% 0.20/0.42    inference(subsumption_resolution,[],[f394,f340])).
% 0.20/0.42  fof(f340,plain,(
% 0.20/0.42    v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = sK1),
% 0.20/0.42    inference(subsumption_resolution,[],[f339,f51])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    l1_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f39])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.42    inference(nnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,negated_conjecture,(
% 0.20/0.42    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.42    inference(negated_conjecture,[],[f15])).
% 0.20/0.42  fof(f15,conjecture,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 0.20/0.42  fof(f339,plain,(
% 0.20/0.42    v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = sK1),
% 0.20/0.42    inference(subsumption_resolution,[],[f335,f52])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.42    inference(cnf_transformation,[],[f39])).
% 0.20/0.42  fof(f335,plain,(
% 0.20/0.42    v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = sK1),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f331])).
% 0.20/0.42  fof(f331,plain,(
% 0.20/0.42    u1_struct_0(sK0) != u1_struct_0(sK0) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = sK1),
% 0.20/0.42    inference(superposition,[],[f61,f288])).
% 0.20/0.42  fof(f288,plain,(
% 0.20/0.42    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | u1_struct_0(sK0) = sK1),
% 0.20/0.42    inference(resolution,[],[f174,f124])).
% 0.20/0.42  fof(f124,plain,(
% 0.20/0.42    v1_subset_1(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1),
% 0.20/0.42    inference(resolution,[],[f52,f73])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(nnf_transformation,[],[f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,axiom,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.42  fof(f174,plain,(
% 0.20/0.42    ~v1_subset_1(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.42    inference(subsumption_resolution,[],[f173,f51])).
% 0.20/0.42  fof(f173,plain,(
% 0.20/0.42    ~v1_subset_1(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f172,f52])).
% 0.20/0.42  fof(f172,plain,(
% 0.20/0.42    ~v1_subset_1(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.42    inference(resolution,[],[f155,f60])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(nnf_transformation,[],[f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.20/0.42  fof(f155,plain,(
% 0.20/0.42    v1_tops_1(sK1,sK0) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.42    inference(subsumption_resolution,[],[f154,f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ~v2_struct_0(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f39])).
% 0.20/0.42  fof(f154,plain,(
% 0.20/0.42    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v1_tops_1(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f153,f49])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    v2_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f39])).
% 0.20/0.42  fof(f153,plain,(
% 0.20/0.42    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v1_tops_1(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f152,f51])).
% 0.20/0.42  fof(f152,plain,(
% 0.20/0.42    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f151,f52])).
% 0.20/0.42  fof(f151,plain,(
% 0.20/0.42    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f150,f146])).
% 0.20/0.42  fof(f146,plain,(
% 0.20/0.42    v3_pre_topc(sK1,sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f145,f49])).
% 0.20/0.42  fof(f145,plain,(
% 0.20/0.42    v3_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f144,f51])).
% 0.20/0.42  fof(f144,plain,(
% 0.20/0.42    v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f122,f50])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    v1_tdlat_3(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f39])).
% 0.20/0.42  fof(f122,plain,(
% 0.20/0.42    v3_pre_topc(sK1,sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.42    inference(resolution,[],[f52,f67])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.42    inference(rectify,[],[f42])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.42    inference(nnf_transformation,[],[f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,axiom,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 0.20/0.42  fof(f150,plain,(
% 0.20/0.42    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v1_tops_1(sK1,sK0) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(resolution,[],[f53,f65])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,axiom,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    v3_tex_2(sK1,sK0) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f39])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f40])).
% 0.20/0.42  fof(f394,plain,(
% 0.20/0.42    u1_struct_0(sK0) = sK1 | ~v1_tops_1(sK1,sK0)),
% 0.20/0.42    inference(backward_demodulation,[],[f129,f392])).
% 0.20/0.42  fof(f392,plain,(
% 0.20/0.42    sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.42    inference(subsumption_resolution,[],[f391,f70])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.42  fof(f391,plain,(
% 0.20/0.42    sK1 = k2_pre_topc(sK0,sK1) | ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.42    inference(resolution,[],[f326,f75])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f47])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.42    inference(nnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.42  fof(f326,plain,(
% 0.20/0.42    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.42    inference(resolution,[],[f196,f96])).
% 0.20/0.42  fof(f96,plain,(
% 0.20/0.42    ( ! [X4] : (v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f95,f51])).
% 0.20/0.42  fof(f95,plain,(
% 0.20/0.42    ( ! [X4] : (v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f91,f50])).
% 0.20/0.42  fof(f91,plain,(
% 0.20/0.42    ( ! [X4] : (v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.42    inference(resolution,[],[f49,f67])).
% 0.20/0.42  fof(f196,plain,(
% 0.20/0.42    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.42    inference(forward_demodulation,[],[f195,f125])).
% 0.20/0.42  fof(f125,plain,(
% 0.20/0.42    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 0.20/0.42    inference(resolution,[],[f52,f71])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f33])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.42  fof(f195,plain,(
% 0.20/0.42    sK1 = k2_pre_topc(sK0,sK1) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f194,f51])).
% 0.20/0.42  fof(f194,plain,(
% 0.20/0.42    sK1 = k2_pre_topc(sK0,sK1) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f192,f52])).
% 0.20/0.42  fof(f192,plain,(
% 0.20/0.42    sK1 = k2_pre_topc(sK0,sK1) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.42    inference(resolution,[],[f126,f63])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f41])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(nnf_transformation,[],[f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 0.20/0.42  fof(f126,plain,(
% 0.20/0.42    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.42    inference(subsumption_resolution,[],[f113,f51])).
% 0.20/0.42  fof(f113,plain,(
% 0.20/0.42    sK1 = k2_pre_topc(sK0,sK1) | ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.42    inference(resolution,[],[f52,f58])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.42  fof(f129,plain,(
% 0.20/0.42    ~v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.42    inference(subsumption_resolution,[],[f115,f51])).
% 0.20/0.42  fof(f115,plain,(
% 0.20/0.42    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.42    inference(resolution,[],[f52,f60])).
% 0.20/0.42  fof(f452,plain,(
% 0.20/0.42    v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.42    inference(subsumption_resolution,[],[f400,f405])).
% 0.20/0.42  fof(f400,plain,(
% 0.20/0.42    u1_struct_0(sK0) != sK1 | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.42    inference(backward_demodulation,[],[f234,f392])).
% 0.20/0.42  fof(f234,plain,(
% 0.20/0.42    v1_subset_1(sK1,u1_struct_0(sK0)) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)),
% 0.20/0.42    inference(resolution,[],[f216,f54])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ~v3_tex_2(sK1,sK0) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f39])).
% 0.20/0.42  fof(f216,plain,(
% 0.20/0.42    v3_tex_2(sK1,sK0) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)),
% 0.20/0.42    inference(subsumption_resolution,[],[f215,f48])).
% 0.20/0.42  fof(f215,plain,(
% 0.20/0.42    u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | v3_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f214,f49])).
% 0.20/0.42  fof(f214,plain,(
% 0.20/0.42    u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | v3_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f213,f51])).
% 0.20/0.42  fof(f213,plain,(
% 0.20/0.42    u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f212,f52])).
% 0.20/0.42  fof(f212,plain,(
% 0.20/0.42    u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | v3_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f210,f136])).
% 0.20/0.42  fof(f136,plain,(
% 0.20/0.42    v2_tex_2(sK1,sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f135,f48])).
% 0.20/0.42  fof(f135,plain,(
% 0.20/0.42    v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f134,f49])).
% 0.20/0.42  fof(f134,plain,(
% 0.20/0.42    v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f133,f50])).
% 0.20/0.42  fof(f133,plain,(
% 0.20/0.42    v2_tex_2(sK1,sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f119,f51])).
% 0.20/0.42  fof(f119,plain,(
% 0.20/0.42    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(resolution,[],[f52,f64])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,axiom,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.20/0.42  fof(f210,plain,(
% 0.20/0.42    u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.42    inference(resolution,[],[f130,f66])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f30])).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.42    inference(flattening,[],[f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,axiom,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.20/0.42  fof(f130,plain,(
% 0.20/0.42    v1_tops_1(sK1,sK0) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)),
% 0.20/0.42    inference(subsumption_resolution,[],[f116,f51])).
% 0.20/0.42  fof(f116,plain,(
% 0.20/0.42    v1_tops_1(sK1,sK0) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.42    inference(resolution,[],[f52,f61])).
% 0.20/0.42  fof(f462,plain,(
% 0.20/0.42    ~v1_subset_1(sK1,sK1)),
% 0.20/0.42    inference(resolution,[],[f406,f76])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.42    inference(equality_resolution,[],[f72])).
% 0.20/0.42  fof(f72,plain,(
% 0.20/0.42    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f46])).
% 0.20/0.42  fof(f406,plain,(
% 0.20/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.42    inference(backward_demodulation,[],[f52,f405])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (29117)------------------------------
% 0.20/0.42  % (29117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (29117)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (29117)Memory used [KB]: 1663
% 0.20/0.42  % (29117)Time elapsed: 0.053 s
% 0.20/0.42  % (29117)------------------------------
% 0.20/0.42  % (29117)------------------------------
% 0.20/0.43  % (29112)Success in time 0.085 s
%------------------------------------------------------------------------------
