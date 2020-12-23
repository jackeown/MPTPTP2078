%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 362 expanded)
%              Number of leaves         :   10 (  95 expanded)
%              Depth                    :   19
%              Number of atoms          :  234 (2429 expanded)
%              Number of equality atoms :   43 (  84 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(resolution,[],[f131,f115])).

fof(f115,plain,(
    ~ v6_tops_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( sK1 != sK1
    | ~ v6_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f110,f50])).

fof(f50,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f49,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ v6_tops_1(sK1,sK0)
      | ~ v5_tops_1(sK1,sK0) )
    & ( v6_tops_1(sK1,sK0)
      | v5_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v6_tops_1(X1,X0)
              | ~ v5_tops_1(X1,X0) )
            & ( v6_tops_1(X1,X0)
              | v5_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v6_tops_1(X1,sK0)
            | ~ v5_tops_1(X1,sK0) )
          & ( v6_tops_1(X1,sK0)
            | v5_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ( ~ v6_tops_1(X1,sK0)
          | ~ v5_tops_1(X1,sK0) )
        & ( v6_tops_1(X1,sK0)
          | v5_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v6_tops_1(sK1,sK0)
        | ~ v5_tops_1(sK1,sK0) )
      & ( v6_tops_1(sK1,sK0)
        | v5_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v4_pre_topc(X1,X0)
                & v3_pre_topc(X1,X0) )
             => ( v5_tops_1(X1,X0)
              <=> v6_tops_1(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0) )
           => ( v5_tops_1(X1,X0)
            <=> v6_tops_1(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tops_1)).

fof(f49,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f48,f31])).

fof(f31,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f110,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v6_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f81,f107])).

fof(f107,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f101,f45])).

fof(f45,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f101,plain,(
    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f84,f100])).

fof(f100,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f99,f29])).

fof(f99,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f98,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f98,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f53,f29])).

fof(f53,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f52,f48])).

fof(f52,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f51,f30])).

fof(f30,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f41,f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f84,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f78,f29])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f34,f28])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f81,plain,
    ( ~ v6_tops_1(sK1,sK0)
    | sK1 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f79,f33])).

fof(f33,plain,
    ( ~ v5_tops_1(sK1,sK0)
    | ~ v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,
    ( v5_tops_1(sK1,sK0)
    | sK1 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f77,f29])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0
      | v5_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f131,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(resolution,[],[f111,f29])).

fof(f111,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v6_tops_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v6_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f71,f107])).

fof(f71,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v6_tops_1(sK1,sK0) ),
    inference(superposition,[],[f67,f50])).

fof(f67,plain,(
    ! [X0] :
      ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) != X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v6_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f38,f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:13:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (13360)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.49  % (13360)Refutation not found, incomplete strategy% (13360)------------------------------
% 0.22/0.49  % (13360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13360)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (13360)Memory used [KB]: 6140
% 0.22/0.49  % (13360)Time elapsed: 0.071 s
% 0.22/0.49  % (13360)------------------------------
% 0.22/0.49  % (13360)------------------------------
% 0.22/0.50  % (13365)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (13381)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (13368)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (13361)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (13359)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (13367)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (13363)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (13368)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(resolution,[],[f131,f115])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    ~v6_tops_1(sK1,sK0)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f114])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    sK1 != sK1 | ~v6_tops_1(sK1,sK0)),
% 0.22/0.51    inference(forward_demodulation,[],[f110,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f49,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ((~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)) & (v6_tops_1(sK1,sK0) | v5_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v6_tops_1(X1,sK0) | ~v5_tops_1(X1,sK0)) & (v6_tops_1(X1,sK0) | v5_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ? [X1] : ((~v6_tops_1(X1,sK0) | ~v5_tops_1(X1,sK0)) & (v6_tops_1(X1,sK0) | v5_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)) & (v6_tops_1(sK1,sK0) | v5_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tops_1)).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f48,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    v4_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 0.22/0.51    inference(resolution,[],[f35,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    sK1 != k2_pre_topc(sK0,sK1) | ~v6_tops_1(sK1,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f81,f107])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    sK1 = k1_tops_1(sK0,sK1)),
% 0.22/0.51    inference(forward_demodulation,[],[f101,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.51    inference(resolution,[],[f44,f29])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1)),
% 0.22/0.51    inference(backward_demodulation,[],[f84,f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.51    inference(resolution,[],[f99,f29])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.51    inference(resolution,[],[f98,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.51    inference(resolution,[],[f53,f29])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.51    inference(resolution,[],[f52,f48])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(resolution,[],[f51,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    v3_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.22/0.51    inference(resolution,[],[f41,f28])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.51    inference(resolution,[],[f78,f29])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 0.22/0.51    inference(resolution,[],[f34,f28])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ~v6_tops_1(sK1,sK0) | sK1 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f79,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ~v5_tops_1(sK1,sK0) | ~v6_tops_1(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    v5_tops_1(sK1,sK0) | sK1 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 0.22/0.51    inference(resolution,[],[f77,f29])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k1_tops_1(sK0,X0)) != X0 | v5_tops_1(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f40,f28])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v5_tops_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    v6_tops_1(sK1,sK0)),
% 0.22/0.51    inference(resolution,[],[f111,f29])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v6_tops_1(sK1,sK0)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v6_tops_1(sK1,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f71,f107])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    sK1 != k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v6_tops_1(sK1,sK0)),
% 0.22/0.51    inference(superposition,[],[f67,f50])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tops_1(sK0,k2_pre_topc(sK0,X0)) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v6_tops_1(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f38,f28])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v6_tops_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (13368)------------------------------
% 0.22/0.51  % (13368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13368)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (13368)Memory used [KB]: 1663
% 0.22/0.51  % (13368)Time elapsed: 0.094 s
% 0.22/0.51  % (13368)------------------------------
% 0.22/0.51  % (13368)------------------------------
% 0.22/0.51  % (13367)Refutation not found, incomplete strategy% (13367)------------------------------
% 0.22/0.51  % (13367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13362)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (13367)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13367)Memory used [KB]: 10618
% 0.22/0.51  % (13367)Time elapsed: 0.109 s
% 0.22/0.51  % (13367)------------------------------
% 0.22/0.51  % (13367)------------------------------
% 0.22/0.51  % (13362)Refutation not found, incomplete strategy% (13362)------------------------------
% 0.22/0.51  % (13362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13362)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (13362)Memory used [KB]: 10618
% 0.22/0.51  % (13362)Time elapsed: 0.102 s
% 0.22/0.51  % (13362)------------------------------
% 0.22/0.51  % (13362)------------------------------
% 0.22/0.51  % (13373)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (13370)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (13375)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (13379)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (13375)Refutation not found, incomplete strategy% (13375)------------------------------
% 0.22/0.52  % (13375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13375)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13375)Memory used [KB]: 1663
% 0.22/0.52  % (13375)Time elapsed: 0.104 s
% 0.22/0.52  % (13375)------------------------------
% 0.22/0.52  % (13375)------------------------------
% 0.22/0.52  % (13379)Refutation not found, incomplete strategy% (13379)------------------------------
% 0.22/0.52  % (13379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13379)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13379)Memory used [KB]: 6140
% 0.22/0.52  % (13379)Time elapsed: 0.113 s
% 0.22/0.52  % (13379)------------------------------
% 0.22/0.52  % (13379)------------------------------
% 0.22/0.52  % (13369)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (13356)Success in time 0.158 s
%------------------------------------------------------------------------------
