%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 (4136 expanded)
%              Number of leaves         :   18 (1409 expanded)
%              Depth                    :   44
%              Number of atoms          :  494 (28310 expanded)
%              Number of equality atoms :   57 (3489 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f352,plain,(
    $false ),
    inference(subsumption_resolution,[],[f351,f69])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f45,f46])).

fof(f46,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ v2_compts_1(sK3,sK1)
      | ~ v2_compts_1(sK2,sK0) )
    & ( v2_compts_1(sK3,sK1)
      | v2_compts_1(sK2,sK0) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f32,f31,f30,f29])).

% (4150)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) )
                    & ( v2_compts_1(X3,X1)
                      | v2_compts_1(X2,X0) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,sK0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,sK0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v2_compts_1(X3,X1)
                  | ~ v2_compts_1(X2,sK0) )
                & ( v2_compts_1(X3,X1)
                  | v2_compts_1(X2,sK0) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v2_compts_1(X3,sK1)
                | ~ v2_compts_1(X2,sK0) )
              & ( v2_compts_1(X3,sK1)
                | v2_compts_1(X2,sK0) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v2_compts_1(X3,sK1)
              | ~ v2_compts_1(X2,sK0) )
            & ( v2_compts_1(X3,sK1)
              | v2_compts_1(X2,sK0) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ~ v2_compts_1(X3,sK1)
            | ~ v2_compts_1(sK2,sK0) )
          & ( v2_compts_1(X3,sK1)
            | v2_compts_1(sK2,sK0) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ( ~ v2_compts_1(X3,sK1)
          | ~ v2_compts_1(sK2,sK0) )
        & ( v2_compts_1(X3,sK1)
          | v2_compts_1(sK2,sK0) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ~ v2_compts_1(sK3,sK1)
        | ~ v2_compts_1(sK2,sK0) )
      & ( v2_compts_1(sK3,sK1)
        | v2_compts_1(sK2,sK0) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( v2_compts_1(X2,X0)
                      <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

% (4136)Refutation not found, incomplete strategy% (4136)------------------------------
% (4136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f351,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f350,f299])).

fof(f299,plain,(
    r1_tarski(sK2,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f116,f295])).

fof(f295,plain,(
    k2_pre_topc(sK1,u1_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f294,f73])).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f72,f43])).

fof(f43,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f51,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f294,plain,
    ( k2_pre_topc(sK1,u1_struct_0(sK1)) = k2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f292,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f50,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f292,plain,
    ( k2_pre_topc(sK1,u1_struct_0(sK1)) = k2_struct_0(sK1)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f290,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f290,plain,(
    v1_tops_1(u1_struct_0(sK1),sK1) ),
    inference(subsumption_resolution,[],[f286,f107])).

fof(f107,plain,(
    r1_tarski(sK5(sK1),u1_struct_0(sK1)) ),
    inference(resolution,[],[f104,f75])).

fof(f75,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(resolution,[],[f63,f70])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f104,plain,(
    ! [X1] :
      ( ~ r1_tarski(u1_struct_0(sK1),X1)
      | r1_tarski(sK5(sK1),X1) ) ),
    inference(resolution,[],[f83,f73])).

fof(f83,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(X4)
      | r1_tarski(sK5(X4),X5)
      | ~ r1_tarski(u1_struct_0(X4),X5) ) ),
    inference(resolution,[],[f65,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r1_tarski(sK5(X0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f61,f63])).

fof(f61,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_tops_1(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_tops_1(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_tops_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f286,plain,
    ( ~ r1_tarski(sK5(sK1),u1_struct_0(sK1))
    | v1_tops_1(u1_struct_0(sK1),sK1) ),
    inference(resolution,[],[f285,f70])).

fof(f285,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(sK5(sK1),X0)
      | v1_tops_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f283,f73])).

fof(f283,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(sK5(sK1),X0)
      | v1_tops_1(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f281,f61])).

fof(f281,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(sK5(sK1),X0)
      | v1_tops_1(X0,sK1) ) ),
    inference(resolution,[],[f218,f213])).

fof(f213,plain,(
    v1_tops_1(sK5(sK1),sK1) ),
    inference(subsumption_resolution,[],[f212,f107])).

fof(f212,plain,
    ( v1_tops_1(sK5(sK1),sK1)
    | ~ r1_tarski(sK5(sK1),u1_struct_0(sK1)) ),
    inference(resolution,[],[f210,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f210,plain,
    ( ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(sK5(sK1),sK1) ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_tops_1(sK5(sK1),sK1) ),
    inference(superposition,[],[f198,f176])).

fof(f176,plain,(
    k2_pre_topc(sK1,sK5(sK1)) = k2_struct_0(sK1) ),
    inference(resolution,[],[f174,f73])).

fof(f174,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,sK5(X0)) ) ),
    inference(subsumption_resolution,[],[f173,f61])).

fof(f173,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,sK5(X0))
      | ~ m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f58,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v1_tops_1(sK5(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f198,plain,(
    ! [X1] :
      ( k2_pre_topc(sK1,X1) != k2_struct_0(sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v1_tops_1(X1,sK1) ) ),
    inference(resolution,[],[f59,f73])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f218,plain,(
    ! [X2,X3] :
      ( ~ v1_tops_1(X2,sK1)
      | ~ r1_tarski(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
      | v1_tops_1(X3,sK1) ) ),
    inference(resolution,[],[f60,f73])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

fof(f116,plain,(
    r1_tarski(sK2,k2_pre_topc(sK1,u1_struct_0(sK1))) ),
    inference(resolution,[],[f109,f82])).

fof(f82,plain,(
    ! [X3] :
      ( ~ r1_tarski(u1_struct_0(sK1),X3)
      | r1_tarski(sK2,X3) ) ),
    inference(resolution,[],[f65,f77])).

fof(f77,plain,(
    r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f63,f69])).

fof(f109,plain,(
    r1_tarski(u1_struct_0(sK1),k2_pre_topc(sK1,u1_struct_0(sK1))) ),
    inference(resolution,[],[f85,f70])).

fof(f85,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | r1_tarski(X1,k2_pre_topc(sK1,X1)) ) ),
    inference(resolution,[],[f57,f73])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f350,plain,
    ( ~ r1_tarski(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f349,f346])).

fof(f346,plain,(
    ~ v2_compts_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f68,f345])).

fof(f345,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f344,f42])).

fof(f344,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f343,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f343,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_compts_1(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_compts_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_compts_1(sK2,sK0) ),
    inference(resolution,[],[f341,f43])).

fof(f341,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(sK2,X0)
      | ~ l1_pre_topc(X0)
      | v2_compts_1(sK2,sK0) ) ),
    inference(resolution,[],[f340,f67])).

fof(f67,plain,
    ( v2_compts_1(sK2,sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f47,f46])).

fof(f47,plain,
    ( v2_compts_1(sK3,sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f340,plain,(
    ! [X0] :
      ( ~ v2_compts_1(sK2,sK1)
      | v2_compts_1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f339,f299])).

fof(f339,plain,(
    ! [X0] :
      ( ~ v2_compts_1(sK2,sK1)
      | v2_compts_1(sK2,X0)
      | ~ r1_tarski(sK2,k2_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f56,f338])).

fof(f338,plain,(
    sK2 = sK4(sK1,sK2) ),
    inference(subsumption_resolution,[],[f337,f315])).

fof(f315,plain,
    ( ~ v2_compts_1(sK2,sK1)
    | sK2 = sK4(sK1,sK2) ),
    inference(resolution,[],[f305,f68])).

fof(f305,plain,
    ( v2_compts_1(sK2,sK0)
    | sK2 = sK4(sK1,sK2) ),
    inference(subsumption_resolution,[],[f303,f44])).

fof(f303,plain,
    ( sK2 = sK4(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_compts_1(sK2,sK0) ),
    inference(resolution,[],[f299,f262])).

fof(f262,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK1))
      | sK4(sK1,X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_compts_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f261,f42])).

fof(f261,plain,(
    ! [X0] :
      ( sK4(sK1,X0) = X0
      | ~ r1_tarski(X0,k2_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_compts_1(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | sK4(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK4(X1,X2),X1)
                    & sK4(X1,X2) = X2
                    & m1_subset_1(sK4(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK4(X1,X2),X1)
        & sK4(X1,X2) = X2
        & m1_subset_1(sK4(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

fof(f337,plain,
    ( v2_compts_1(sK2,sK1)
    | sK2 = sK4(sK1,sK2) ),
    inference(subsumption_resolution,[],[f336,f299])).

fof(f336,plain,
    ( v2_compts_1(sK2,sK1)
    | ~ r1_tarski(sK2,k2_struct_0(sK1))
    | sK2 = sK4(sK1,sK2) ),
    inference(subsumption_resolution,[],[f335,f69])).

fof(f335,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_compts_1(sK2,sK1)
    | ~ r1_tarski(sK2,k2_struct_0(sK1))
    | sK2 = sK4(sK1,sK2) ),
    inference(resolution,[],[f317,f43])).

fof(f317,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(sK2,X0)
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | sK2 = sK4(sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f316,f42])).

fof(f316,plain,(
    ! [X0] :
      ( sK2 = sK4(sK1,sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(sK2,X0)
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f305,f71])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( ~ v2_compts_1(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X4,X1)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f66,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( v2_compts_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_compts_1(sK4(X1,X2),X1)
      | v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | ~ v2_compts_1(sK2,sK1) ),
    inference(backward_demodulation,[],[f48,f46])).

fof(f48,plain,
    ( ~ v2_compts_1(sK3,sK1)
    | ~ v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f349,plain,
    ( v2_compts_1(sK2,sK1)
    | ~ r1_tarski(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f348,f43])).

fof(f348,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_compts_1(sK2,X0)
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f347,f42])).

fof(f347,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(sK2,X0)
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f345,f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:52:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (4135)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (4151)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (4132)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (4134)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (4154)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (4153)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (4149)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (4138)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (4139)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (4133)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (4146)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (4145)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (4143)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (4131)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (4141)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (4138)Refutation not found, incomplete strategy% (4138)------------------------------
% 0.21/0.52  % (4138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4137)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (4155)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (4138)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4138)Memory used [KB]: 1791
% 0.21/0.52  % (4138)Time elapsed: 0.108 s
% 0.21/0.52  % (4138)------------------------------
% 0.21/0.52  % (4138)------------------------------
% 0.21/0.52  % (4131)Refutation not found, incomplete strategy% (4131)------------------------------
% 0.21/0.52  % (4131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4136)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (4131)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4131)Memory used [KB]: 10618
% 0.21/0.53  % (4131)Time elapsed: 0.115 s
% 0.21/0.53  % (4131)------------------------------
% 0.21/0.53  % (4131)------------------------------
% 0.21/0.53  % (4140)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (4134)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (4147)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (4152)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (4142)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (4144)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (4148)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f352,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f351,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.55    inference(forward_demodulation,[],[f45,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    sK2 = sK3),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ((((~v2_compts_1(sK3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(sK3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f32,f31,f30,f29])).
% 0.21/0.55  % (4150)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(X1,sK0)) => (? [X2] : (? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(sK1,sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ? [X2] : (? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => ((~v2_compts_1(sK3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(sK3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 0.21/0.55    inference(negated_conjecture,[],[f12])).
% 0.21/0.55  % (4136)Refutation not found, incomplete strategy% (4136)------------------------------
% 0.21/0.55  % (4136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  fof(f12,conjecture,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f351,plain,(
% 0.21/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f350,f299])).
% 0.21/0.55  fof(f299,plain,(
% 0.21/0.55    r1_tarski(sK2,k2_struct_0(sK1))),
% 0.21/0.55    inference(backward_demodulation,[],[f116,f295])).
% 0.21/0.55  fof(f295,plain,(
% 0.21/0.55    k2_pre_topc(sK1,u1_struct_0(sK1)) = k2_struct_0(sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f294,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    l1_pre_topc(sK1)),
% 0.21/0.55    inference(resolution,[],[f72,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    m1_pre_topc(sK1,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.21/0.55    inference(resolution,[],[f51,f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    l1_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.55  fof(f294,plain,(
% 0.21/0.55    k2_pre_topc(sK1,u1_struct_0(sK1)) = k2_struct_0(sK1) | ~l1_pre_topc(sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f292,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f50,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.55  fof(f292,plain,(
% 0.21/0.55    k2_pre_topc(sK1,u1_struct_0(sK1)) = k2_struct_0(sK1) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.21/0.55    inference(resolution,[],[f290,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.21/0.55  fof(f290,plain,(
% 0.21/0.55    v1_tops_1(u1_struct_0(sK1),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f286,f107])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    r1_tarski(sK5(sK1),u1_struct_0(sK1))),
% 0.21/0.55    inference(resolution,[],[f104,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f63,f70])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ( ! [X1] : (~r1_tarski(u1_struct_0(sK1),X1) | r1_tarski(sK5(sK1),X1)) )),
% 0.21/0.55    inference(resolution,[],[f83,f73])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~l1_pre_topc(X4) | r1_tarski(sK5(X4),X5) | ~r1_tarski(u1_struct_0(X4),X5)) )),
% 0.21/0.55    inference(resolution,[],[f65,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(sK5(X0),u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(resolution,[],[f61,f63])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0] : ((v1_tops_1(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_1(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_tops_1)).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(flattening,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.55  fof(f286,plain,(
% 0.21/0.55    ~r1_tarski(sK5(sK1),u1_struct_0(sK1)) | v1_tops_1(u1_struct_0(sK1),sK1)),
% 0.21/0.55    inference(resolution,[],[f285,f70])).
% 0.21/0.55  fof(f285,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK5(sK1),X0) | v1_tops_1(X0,sK1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f283,f73])).
% 0.21/0.55  fof(f283,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK5(sK1),X0) | v1_tops_1(X0,sK1) | ~l1_pre_topc(sK1)) )),
% 0.21/0.55    inference(resolution,[],[f281,f61])).
% 0.21/0.55  fof(f281,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(sK5(sK1),X0) | v1_tops_1(X0,sK1)) )),
% 0.21/0.55    inference(resolution,[],[f218,f213])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    v1_tops_1(sK5(sK1),sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f212,f107])).
% 0.21/0.55  fof(f212,plain,(
% 0.21/0.55    v1_tops_1(sK5(sK1),sK1) | ~r1_tarski(sK5(sK1),u1_struct_0(sK1))),
% 0.21/0.55    inference(resolution,[],[f210,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f41])).
% 0.21/0.55  fof(f210,plain,(
% 0.21/0.55    ~m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | v1_tops_1(sK5(sK1),sK1)),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f209])).
% 0.21/0.55  fof(f209,plain,(
% 0.21/0.55    k2_struct_0(sK1) != k2_struct_0(sK1) | ~m1_subset_1(sK5(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | v1_tops_1(sK5(sK1),sK1)),
% 0.21/0.55    inference(superposition,[],[f198,f176])).
% 0.21/0.55  fof(f176,plain,(
% 0.21/0.55    k2_pre_topc(sK1,sK5(sK1)) = k2_struct_0(sK1)),
% 0.21/0.55    inference(resolution,[],[f174,f73])).
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,sK5(X0))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f173,f61])).
% 0.21/0.55  fof(f173,plain,(
% 0.21/0.55    ( ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,sK5(X0)) | ~m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f172])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    ( ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,sK5(X0)) | ~m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(resolution,[],[f58,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0] : (v1_tops_1(sK5(X0),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f40])).
% 0.21/0.55  fof(f198,plain,(
% 0.21/0.55    ( ! [X1] : (k2_pre_topc(sK1,X1) != k2_struct_0(sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v1_tops_1(X1,sK1)) )),
% 0.21/0.55    inference(resolution,[],[f59,f73])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f38])).
% 0.21/0.55  fof(f218,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~v1_tops_1(X2,sK1) | ~r1_tarski(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | v1_tops_1(X3,sK1)) )),
% 0.21/0.55    inference(resolution,[],[f60,f73])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X2,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    r1_tarski(sK2,k2_pre_topc(sK1,u1_struct_0(sK1)))),
% 0.21/0.55    inference(resolution,[],[f109,f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X3] : (~r1_tarski(u1_struct_0(sK1),X3) | r1_tarski(sK2,X3)) )),
% 0.21/0.55    inference(resolution,[],[f65,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    r1_tarski(sK2,u1_struct_0(sK1))),
% 0.21/0.55    inference(resolution,[],[f63,f69])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(sK1),k2_pre_topc(sK1,u1_struct_0(sK1)))),
% 0.21/0.55    inference(resolution,[],[f85,f70])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(X1,k2_pre_topc(sK1,X1))) )),
% 0.21/0.55    inference(resolution,[],[f57,f73])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.21/0.55  fof(f350,plain,(
% 0.21/0.55    ~r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f349,f346])).
% 0.21/0.55  fof(f346,plain,(
% 0.21/0.55    ~v2_compts_1(sK2,sK1)),
% 0.21/0.55    inference(subsumption_resolution,[],[f68,f345])).
% 0.21/0.55  fof(f345,plain,(
% 0.21/0.55    v2_compts_1(sK2,sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f344,f42])).
% 0.21/0.55  fof(f344,plain,(
% 0.21/0.55    v2_compts_1(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f343,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f343,plain,(
% 0.21/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(sK2,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f342])).
% 0.21/0.55  fof(f342,plain,(
% 0.21/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(sK2,sK0) | ~l1_pre_topc(sK0) | v2_compts_1(sK2,sK0)),
% 0.21/0.55    inference(resolution,[],[f341,f43])).
% 0.21/0.55  fof(f341,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK2,X0) | ~l1_pre_topc(X0) | v2_compts_1(sK2,sK0)) )),
% 0.21/0.55    inference(resolution,[],[f340,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    v2_compts_1(sK2,sK1) | v2_compts_1(sK2,sK0)),
% 0.21/0.55    inference(backward_demodulation,[],[f47,f46])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    v2_compts_1(sK3,sK1) | v2_compts_1(sK2,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f340,plain,(
% 0.21/0.55    ( ! [X0] : (~v2_compts_1(sK2,sK1) | v2_compts_1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f339,f299])).
% 0.21/0.55  fof(f339,plain,(
% 0.21/0.55    ( ! [X0] : (~v2_compts_1(sK2,sK1) | v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(superposition,[],[f56,f338])).
% 0.21/0.55  fof(f338,plain,(
% 0.21/0.55    sK2 = sK4(sK1,sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f337,f315])).
% 0.21/0.55  fof(f315,plain,(
% 0.21/0.55    ~v2_compts_1(sK2,sK1) | sK2 = sK4(sK1,sK2)),
% 0.21/0.55    inference(resolution,[],[f305,f68])).
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    v2_compts_1(sK2,sK0) | sK2 = sK4(sK1,sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f303,f44])).
% 0.21/0.55  fof(f303,plain,(
% 0.21/0.55    sK2 = sK4(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(sK2,sK0)),
% 0.21/0.55    inference(resolution,[],[f299,f262])).
% 0.21/0.55  fof(f262,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK1)) | sK4(sK1,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X0,sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f261,f42])).
% 0.21/0.55  fof(f261,plain,(
% 0.21/0.55    ( ! [X0] : (sK4(sK1,X0) = X0 | ~r1_tarski(X0,k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.55    inference(resolution,[],[f55,f43])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | sK4(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK4(X1,X2),X1) & sK4(X1,X2) = X2 & m1_subset_1(sK4(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK4(X1,X2),X1) & sK4(X1,X2) = X2 & m1_subset_1(sK4(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(rectify,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).
% 0.21/0.55  fof(f337,plain,(
% 0.21/0.55    v2_compts_1(sK2,sK1) | sK2 = sK4(sK1,sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f336,f299])).
% 0.21/0.55  fof(f336,plain,(
% 0.21/0.55    v2_compts_1(sK2,sK1) | ~r1_tarski(sK2,k2_struct_0(sK1)) | sK2 = sK4(sK1,sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f335,f69])).
% 0.21/0.55  fof(f335,plain,(
% 0.21/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | v2_compts_1(sK2,sK1) | ~r1_tarski(sK2,k2_struct_0(sK1)) | sK2 = sK4(sK1,sK2)),
% 0.21/0.55    inference(resolution,[],[f317,f43])).
% 0.21/0.55  fof(f317,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(X0)) | sK2 = sK4(sK1,sK2)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f316,f42])).
% 0.21/0.55  fof(f316,plain,(
% 0.21/0.55    ( ! [X0] : (sK2 = sK4(sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.55    inference(resolution,[],[f305,f71])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (~v2_compts_1(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_compts_1(X4,X1) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f66,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X4,X0,X1] : (v2_compts_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v2_compts_1(sK4(X1,X2),X1) | v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ~v2_compts_1(sK2,sK0) | ~v2_compts_1(sK2,sK1)),
% 0.21/0.55    inference(backward_demodulation,[],[f48,f46])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ~v2_compts_1(sK3,sK1) | ~v2_compts_1(sK2,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f349,plain,(
% 0.21/0.55    v2_compts_1(sK2,sK1) | ~r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.55    inference(resolution,[],[f348,f43])).
% 0.21/0.55  fof(f348,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f347,f42])).
% 0.21/0.55  fof(f347,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.55    inference(resolution,[],[f345,f71])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (4134)------------------------------
% 0.21/0.55  % (4134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4134)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (4134)Memory used [KB]: 6396
% 0.21/0.55  % (4134)Time elapsed: 0.122 s
% 0.21/0.55  % (4134)------------------------------
% 0.21/0.55  % (4134)------------------------------
% 0.21/0.55  % (4130)Success in time 0.188 s
%------------------------------------------------------------------------------
