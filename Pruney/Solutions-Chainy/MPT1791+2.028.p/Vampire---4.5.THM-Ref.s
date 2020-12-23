%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 (1548 expanded)
%              Number of leaves         :    9 ( 408 expanded)
%              Depth                    :   36
%              Number of atoms          :  367 (10194 expanded)
%              Number of equality atoms :   84 (2244 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(resolution,[],[f148,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) )
            & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
            | ~ v3_pre_topc(X1,sK0) )
          & ( k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ( k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          | ~ v3_pre_topc(X1,sK0) )
        & ( k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ v3_pre_topc(X1,X0) )
          & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ v3_pre_topc(X1,X0) )
          & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f148,plain,(
    v2_struct_0(sK0) ),
    inference(resolution,[],[f147,f132])).

fof(f132,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f103,f126])).

fof(f126,plain,(
    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0)) ),
    inference(backward_demodulation,[],[f98,f125])).

fof(f125,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f84,f122])).

fof(f122,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f114,f72])).

fof(f72,plain,(
    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f70,f28])).

fof(f70,plain,
    ( v2_struct_0(sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f68,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f64,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f38,f29])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

% (21340)Refutation not found, incomplete strategy% (21340)------------------------------
% (21340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21340)Termination reason: Refutation not found, incomplete strategy

% (21340)Memory used [KB]: 6140
% (21340)Time elapsed: 0.105 s
% (21340)------------------------------
% (21340)------------------------------
fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f114,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK1))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f96,f112])).

fof(f112,plain,
    ( k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f111,f28])).

fof(f111,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0)) ),
    inference(resolution,[],[f99,f31])).

fof(f99,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f90,f98])).

fof(f90,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | v2_struct_0(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f88,f55])).

fof(f55,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f46,f31])).

fof(f46,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f34,f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f88,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f77,f30])).

fof(f77,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f39,f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f96,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0))) ),
    inference(backward_demodulation,[],[f78,f95])).

fof(f95,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) ),
    inference(resolution,[],[f94,f30])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) ),
    inference(resolution,[],[f93,f29])).

fof(f93,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) ),
    inference(resolution,[],[f92,f28])).

fof(f92,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f89,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK2(X0),X0)
        & v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK2(X0),X0)
        & v3_pre_topc(sK2(X0),X0)
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_tops_1)).

fof(f89,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f88,f50])).

fof(f50,plain,
    ( r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f49,f29])).

fof(f49,plain,
    ( ~ v2_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f47,f41])).

fof(f47,plain,
    ( ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f45,f29])).

fof(f45,plain,
    ( ~ v2_pre_topc(sK0)
    | r2_hidden(sK2(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f44,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v3_pre_topc(sK2(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f76,f30])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f75,f29])).

fof(f75,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f71,f28])).

fof(f71,plain,
    ( v2_struct_0(sK0)
    | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f68,f41])).

fof(f84,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f82,f28])).

fof(f82,plain,
    ( v2_struct_0(sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f81,f31])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f69,f30])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f36,f29])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f98,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(sK0)) ),
    inference(backward_demodulation,[],[f87,f95])).

fof(f87,plain,(
    k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f86,f30])).

fof(f86,plain,
    ( ~ l1_pre_topc(sK0)
    | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f85,f29])).

fof(f85,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0))) ),
    inference(resolution,[],[f83,f28])).

fof(f83,plain,
    ( v2_struct_0(sK0)
    | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f81,f41])).

fof(f103,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK2(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f33,f98])).

fof(f33,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f147,plain,
    ( v3_pre_topc(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f146,f30])).

fof(f146,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f144,f31])).

fof(f144,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f142,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f142,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f141,f30])).

fof(f141,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f140,f31])).

fof(f140,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f139,f29])).

fof(f139,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | v2_struct_0(sK0) ),
    inference(trivial_inequality_removal,[],[f138])).

fof(f138,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f40,f122])).

fof(f40,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:06:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (21329)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (21330)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.50  % (21323)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (21326)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (21322)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (21324)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (21321)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (21330)Refutation not found, incomplete strategy% (21330)------------------------------
% 0.22/0.51  % (21330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21330)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21330)Memory used [KB]: 10618
% 0.22/0.51  % (21330)Time elapsed: 0.094 s
% 0.22/0.51  % (21330)------------------------------
% 0.22/0.51  % (21330)------------------------------
% 0.22/0.51  % (21341)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (21325)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (21336)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (21327)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (21336)Refutation not found, incomplete strategy% (21336)------------------------------
% 0.22/0.51  % (21336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21336)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21336)Memory used [KB]: 1663
% 0.22/0.51  % (21336)Time elapsed: 0.107 s
% 0.22/0.51  % (21336)------------------------------
% 0.22/0.51  % (21336)------------------------------
% 0.22/0.51  % (21323)Refutation not found, incomplete strategy% (21323)------------------------------
% 0.22/0.51  % (21323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21323)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21323)Memory used [KB]: 10618
% 0.22/0.51  % (21323)Time elapsed: 0.101 s
% 0.22/0.51  % (21323)------------------------------
% 0.22/0.51  % (21323)------------------------------
% 0.22/0.51  % (21342)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (21327)Refutation not found, incomplete strategy% (21327)------------------------------
% 0.22/0.51  % (21327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21327)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21327)Memory used [KB]: 6140
% 0.22/0.51  % (21327)Time elapsed: 0.069 s
% 0.22/0.51  % (21327)------------------------------
% 0.22/0.51  % (21327)------------------------------
% 0.22/0.51  % (21335)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (21340)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (21328)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (21333)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (21329)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(resolution,[],[f148,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(X1,sK0)) & (k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X1] : ((k6_tmap_1(sK0,X1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(X1,sK0)) & (k6_tmap_1(sK0,X1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f6])).
% 0.22/0.51  fof(f6,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f147,f132])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    ~v3_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f131])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f103,f126])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0))),
% 0.22/0.51    inference(backward_demodulation,[],[f98,f125])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(backward_demodulation,[],[f84,f122])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(superposition,[],[f114,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f70,f28])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    v2_struct_0(sK0) | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f68,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f64,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f38,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  % (21340)Refutation not found, incomplete strategy% (21340)------------------------------
% 0.22/0.51  % (21340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21340)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21340)Memory used [KB]: 6140
% 0.22/0.51  % (21340)Time elapsed: 0.105 s
% 0.22/0.51  % (21340)------------------------------
% 0.22/0.51  % (21340)------------------------------
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK1)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(superposition,[],[f96,f112])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f111,f28])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0))),
% 0.22/0.51    inference(resolution,[],[f99,f31])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,sK1) = k6_tmap_1(sK0,sK2(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | v2_struct_0(sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f90,f98])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | v2_struct_0(sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f88,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    r2_hidden(sK1,u1_pre_topc(sK0)) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f46,f31])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,u1_pre_topc(sK0)) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f44,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    v3_pre_topc(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,u1_pre_topc(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f34,f30])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f77,f30])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f39,f29])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(backward_demodulation,[],[f78,f95])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))),
% 0.22/0.51    inference(resolution,[],[f94,f30])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))),
% 0.22/0.51    inference(resolution,[],[f93,f29])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0))),
% 0.22/0.51    inference(resolution,[],[f92,f28])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f89,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : ((v4_pre_topc(sK2(X0),X0) & v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK2(X0),X0) & v3_pre_topc(sK2(X0),X0) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_tops_1)).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ~m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK2(sK0)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f88,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    r2_hidden(sK2(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f49,f29])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | r2_hidden(sK2(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | r2_hidden(sK2(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f47,f41])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r2_hidden(sK2(sK0),u1_pre_topc(sK0))),
% 0.22/0.51    inference(resolution,[],[f45,f29])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | r2_hidden(sK2(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(resolution,[],[f44,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0] : (v3_pre_topc(sK2(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f76,f30])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f75,f29])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f71,f28])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    v2_struct_0(sK0) | k5_tmap_1(sK0,sK2(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK2(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f68,f41])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f82,f28])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    v2_struct_0(sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f81,f31])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f69,f30])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f36,f29])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK2(sK0))),
% 0.22/0.51    inference(backward_demodulation,[],[f87,f95])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f86,f30])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f85,f29])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0)))),
% 0.22/0.51    inference(resolution,[],[f83,f28])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    v2_struct_0(sK0) | k6_tmap_1(sK0,sK2(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK2(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f81,f41])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK2(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f33,f98])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    v3_pre_topc(sK1,sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f146,f30])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v3_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(resolution,[],[f144,f31])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f142,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f142,plain,(
% 0.22/0.51    r2_hidden(sK1,u1_pre_topc(sK0)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f141,f30])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f140,f31])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f139,f29])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | v2_struct_0(sK0)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f138])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    u1_pre_topc(sK0) != u1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(superposition,[],[f40,f122])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (21329)------------------------------
% 0.22/0.51  % (21329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21329)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (21329)Memory used [KB]: 1663
% 0.22/0.51  % (21329)Time elapsed: 0.107 s
% 0.22/0.51  % (21329)------------------------------
% 0.22/0.51  % (21329)------------------------------
% 0.22/0.51  % (21328)Refutation not found, incomplete strategy% (21328)------------------------------
% 0.22/0.51  % (21328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21328)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21328)Memory used [KB]: 10618
% 0.22/0.51  % (21328)Time elapsed: 0.107 s
% 0.22/0.51  % (21328)------------------------------
% 0.22/0.51  % (21328)------------------------------
% 0.22/0.51  % (21338)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (21319)Success in time 0.154 s
%------------------------------------------------------------------------------
