%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  125 (7287 expanded)
%              Number of leaves         :   12 (1462 expanded)
%              Depth                    :   35
%              Number of atoms          :  412 (31494 expanded)
%              Number of equality atoms :   51 (1857 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1054,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1053,f575])).

fof(f575,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f33,f573])).

fof(f573,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f572,f33])).

fof(f572,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f570,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f570,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f569,f67])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f36,f65])).

fof(f65,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f39,f64])).

fof(f64,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f40,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & r1_tarski(X2,X1)
                    & v2_compts_1(X1,X0) )
                 => v2_compts_1(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f569,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f568,f80])).

fof(f80,plain,(
    ! [X0] :
      ( m1_pre_topc(k1_pre_topc(sK0,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f79,f65])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_pre_topc(k1_pre_topc(sK0,X0),sK0) ) ),
    inference(resolution,[],[f55,f38])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f568,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f567,f273])).

fof(f273,plain,
    ( v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f271,f33])).

fof(f271,plain,
    ( ~ r1_tarski(sK2,sK1)
    | v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(superposition,[],[f264,f108])).

fof(f108,plain,(
    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f82,f67])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f81,f65])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ) ),
    inference(resolution,[],[f47,f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

% (4724)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f264,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,u1_struct_0(X0))
      | v4_pre_topc(sK2,X0)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f263,f56])).

fof(f263,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0)
      | v4_pre_topc(sK2,X0) ) ),
    inference(resolution,[],[f239,f34])).

fof(f34,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(resolution,[],[f63,f38])).

fof(f63,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v4_pre_topc(X3,X2) ) ),
    inference(subsumption_resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f61,plain,(
    ! [X2,X0,X3] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v4_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v4_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

fof(f567,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | k1_xboole_0 = sK1
    | ~ v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f566,f342])).

fof(f342,plain,(
    ! [X0] :
      ( v2_compts_1(X0,k1_pre_topc(sK0,sK1))
      | k1_xboole_0 = sK1
      | ~ v4_pre_topc(X0,k1_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) ) ),
    inference(forward_demodulation,[],[f341,f108])).

fof(f341,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | ~ v4_pre_topc(X0,k1_pre_topc(sK0,sK1))
      | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f339,f85])).

fof(f85,plain,(
    l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f83,f67])).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | l1_pre_topc(k1_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f80,f68])).

% (4723)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f68,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f41,f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f339,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
      | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
      | ~ v4_pre_topc(X0,k1_pre_topc(sK0,sK1))
      | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f337,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_compts_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).

fof(f337,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f333,f32])).

fof(f32,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f333,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(resolution,[],[f331,f67])).

fof(f331,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 = X0
      | v1_compts_1(k1_pre_topc(sK0,X0))
      | ~ v2_compts_1(X0,sK0) ) ),
    inference(forward_demodulation,[],[f330,f65])).

fof(f330,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X0
      | v1_compts_1(k1_pre_topc(sK0,X0))
      | ~ v2_compts_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f329,f38])).

fof(f329,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k1_xboole_0 = X0
      | v1_compts_1(k1_pre_topc(sK0,X0))
      | ~ v2_compts_1(X0,sK0) ) ),
    inference(resolution,[],[f49,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = X1
      | v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

fof(f566,plain,
    ( ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f565,f476])).

fof(f476,plain,(
    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f475,f67])).

fof(f475,plain,
    ( sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f474,f80])).

fof(f474,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f472,f33])).

fof(f472,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) ),
    inference(superposition,[],[f467,f114])).

fof(f114,plain,(
    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(backward_demodulation,[],[f101,f108])).

fof(f101,plain,(
    u1_struct_0(k1_pre_topc(sK0,sK1)) = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f96,f39])).

fof(f96,plain,(
    l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f85,f40])).

fof(f467,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | sK2 = sK3(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f462,f35])).

fof(f35,plain,(
    ~ v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f462,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | sK2 = sK3(X0,sK2)
      | v2_compts_1(sK2,sK0) ) ),
    inference(resolution,[],[f459,f66])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f31,f65])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f459,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | sK3(X0,X1) = X1
      | v2_compts_1(X1,sK0) ) ),
    inference(forward_demodulation,[],[f452,f65])).

fof(f452,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | sK3(X0,X1) = X1
      | v2_compts_1(X1,sK0) ) ),
    inference(resolution,[],[f45,f38])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | sK3(X1,X2) = X2
      | v2_compts_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(f565,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ v2_compts_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f563,f33])).

fof(f563,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ v2_compts_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f558,f114])).

fof(f558,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_compts_1(sK3(X0,sK2),X0) ) ),
    inference(subsumption_resolution,[],[f553,f35])).

fof(f553,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ v2_compts_1(sK3(X0,sK2),X0)
      | v2_compts_1(sK2,sK0) ) ),
    inference(resolution,[],[f532,f66])).

fof(f532,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | ~ v2_compts_1(sK3(X0,X1),X0)
      | v2_compts_1(X1,sK0) ) ),
    inference(forward_demodulation,[],[f525,f65])).

fof(f525,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | ~ v2_compts_1(sK3(X0,X1),X0)
      | v2_compts_1(X1,sK0) ) ),
    inference(resolution,[],[f46,f38])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ v2_compts_1(sK3(X1,X2),X1)
      | v2_compts_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f1053,plain,(
    ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(resolution,[],[f1051,f56])).

fof(f1051,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1050,f576])).

fof(f576,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f67,f573])).

fof(f1050,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f1049,f80])).

fof(f1049,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1048,f777])).

fof(f777,plain,
    ( v4_pre_topc(sK2,k1_pre_topc(sK0,k1_xboole_0))
    | ~ m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0) ),
    inference(forward_demodulation,[],[f635,f573])).

fof(f635,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0)
    | v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) ),
    inference(backward_demodulation,[],[f273,f573])).

fof(f1048,plain,
    ( ~ v4_pre_topc(sK2,k1_pre_topc(sK0,k1_xboole_0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0) ),
    inference(resolution,[],[f894,f865])).

fof(f865,plain,
    ( ~ v2_compts_1(sK2,k1_pre_topc(sK0,k1_xboole_0))
    | ~ m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0) ),
    inference(forward_demodulation,[],[f713,f573])).

fof(f713,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0)
    | ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) ),
    inference(backward_demodulation,[],[f566,f573])).

fof(f894,plain,(
    ! [X0] :
      ( v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0))
      | ~ v4_pre_topc(X0,k1_pre_topc(sK0,k1_xboole_0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f893,f582])).

fof(f582,plain,(
    k1_xboole_0 = u1_struct_0(k1_pre_topc(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f108,f573])).

fof(f893,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,k1_xboole_0))))
      | ~ v4_pre_topc(X0,k1_pre_topc(sK0,k1_xboole_0))
      | v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f892,f579])).

fof(f579,plain,(
    l1_pre_topc(k1_pre_topc(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f85,f573])).

fof(f892,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,k1_xboole_0))))
      | ~ l1_pre_topc(k1_pre_topc(sK0,k1_xboole_0))
      | ~ v4_pre_topc(X0,k1_pre_topc(sK0,k1_xboole_0))
      | v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0)) ) ),
    inference(resolution,[],[f721,f52])).

fof(f721,plain,(
    v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f716,f576])).

fof(f716,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f128,f574])).

fof(f574,plain,(
    v2_compts_1(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f32,f573])).

fof(f128,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f124,f38])).

fof(f124,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ v2_compts_1(k1_xboole_0,sK0) ),
    inference(superposition,[],[f59,f65])).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X1
      | v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:42:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (4729)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.46  % (4729)Refutation not found, incomplete strategy% (4729)------------------------------
% 0.21/0.46  % (4729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (4729)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (4729)Memory used [KB]: 1663
% 0.21/0.46  % (4729)Time elapsed: 0.054 s
% 0.21/0.46  % (4729)------------------------------
% 0.21/0.46  % (4729)------------------------------
% 0.21/0.46  % (4741)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.49  % (4726)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (4741)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1054,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f1053,f575])).
% 0.21/0.50  fof(f575,plain,(
% 0.21/0.50    r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.50    inference(backward_demodulation,[],[f33,f573])).
% 0.21/0.50  fof(f573,plain,(
% 0.21/0.50    k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f572,f33])).
% 0.21/0.50  fof(f572,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~r1_tarski(sK2,sK1)),
% 0.21/0.50    inference(resolution,[],[f570,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f570,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f569,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f36,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f39,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    l1_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f40,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(X2,X0) & (v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f569,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(resolution,[],[f568,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0] : (m1_pre_topc(k1_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f79,f65])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(k1_pre_topc(sK0,X0),sK0)) )),
% 0.21/0.50    inference(resolution,[],[f55,f38])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.50  fof(f568,plain,(
% 0.21/0.50    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f567,f273])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f271,f33])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    ~r1_tarski(sK2,sK1) | v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.50    inference(superposition,[],[f264,f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f82,f67])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) )),
% 0.21/0.50    inference(forward_demodulation,[],[f81,f65])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) )),
% 0.21/0.50    inference(resolution,[],[f47,f38])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.50  % (4724)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK2,u1_struct_0(X0)) | v4_pre_topc(sK2,X0) | ~m1_pre_topc(X0,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f263,f56])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK0) | v4_pre_topc(sK2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f239,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v4_pre_topc(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v4_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f63,f38])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v4_pre_topc(X3,X2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f61,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X3] : (~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v4_pre_topc(X3,X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v4_pre_topc(X3,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v4_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
% 0.21/0.50  fof(f567,plain,(
% 0.21/0.50    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | k1_xboole_0 = sK1 | ~v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 0.21/0.50    inference(resolution,[],[f566,f342])).
% 0.21/0.50  fof(f342,plain,(
% 0.21/0.50    ( ! [X0] : (v2_compts_1(X0,k1_pre_topc(sK0,sK1)) | k1_xboole_0 = sK1 | ~v4_pre_topc(X0,k1_pre_topc(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f341,f108])).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = sK1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~v4_pre_topc(X0,k1_pre_topc(sK0,sK1)) | v2_compts_1(X0,k1_pre_topc(sK0,sK1))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f339,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f83,f67])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | l1_pre_topc(k1_pre_topc(sK0,X0))) )),
% 0.21/0.50    inference(resolution,[],[f80,f68])).
% 0.21/0.50  % (4723)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.21/0.50    inference(resolution,[],[f41,f38])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = sK1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~v4_pre_topc(X0,k1_pre_topc(sK0,sK1)) | v2_compts_1(X0,k1_pre_topc(sK0,sK1))) )),
% 0.21/0.50    inference(resolution,[],[f337,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | v2_compts_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    v1_compts_1(k1_pre_topc(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f333,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    v2_compts_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f333,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f331,f67])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = X0 | v1_compts_1(k1_pre_topc(sK0,X0)) | ~v2_compts_1(X0,sK0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f330,f65])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | v1_compts_1(k1_pre_topc(sK0,X0)) | ~v2_compts_1(X0,sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f329,f38])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_xboole_0 = X0 | v1_compts_1(k1_pre_topc(sK0,X0)) | ~v2_compts_1(X0,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f49,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = X1 | v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1 | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1) | ~v2_pre_topc(X0)) & ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 != X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).
% 0.21/0.50  fof(f566,plain,(
% 0.21/0.50    ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.50    inference(forward_demodulation,[],[f565,f476])).
% 0.21/0.50  fof(f476,plain,(
% 0.21/0.50    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f475,f67])).
% 0.21/0.50  fof(f475,plain,(
% 0.21/0.50    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(resolution,[],[f474,f80])).
% 0.21/0.50  fof(f474,plain,(
% 0.21/0.50    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f472,f33])).
% 0.21/0.50  fof(f472,plain,(
% 0.21/0.50    ~r1_tarski(sK2,sK1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)),
% 0.21/0.50    inference(superposition,[],[f467,f114])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(backward_demodulation,[],[f101,f108])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    u1_struct_0(k1_pre_topc(sK0,sK1)) = k2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f96,f39])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    l1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f85,f40])).
% 0.21/0.50  fof(f467,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK2,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | sK2 = sK3(X0,sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f462,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ~v2_compts_1(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f462,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~r1_tarski(sK2,k2_struct_0(X0)) | sK2 = sK3(X0,sK2) | v2_compts_1(sK2,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f459,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f31,f65])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f459,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(X1,k2_struct_0(X0)) | sK3(X0,X1) = X1 | v2_compts_1(X1,sK0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f452,f65])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,k2_struct_0(X0)) | sK3(X0,X1) = X1 | v2_compts_1(X1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f45,f38])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | sK3(X1,X2) = X2 | v2_compts_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).
% 0.21/0.50  fof(f565,plain,(
% 0.21/0.50    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~v2_compts_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f563,f33])).
% 0.21/0.50  fof(f563,plain,(
% 0.21/0.50    ~r1_tarski(sK2,sK1) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~v2_compts_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(superposition,[],[f558,f114])).
% 0.21/0.50  fof(f558,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK2,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~v2_compts_1(sK3(X0,sK2),X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f553,f35])).
% 0.21/0.50  fof(f553,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~r1_tarski(sK2,k2_struct_0(X0)) | ~v2_compts_1(sK3(X0,sK2),X0) | v2_compts_1(sK2,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f532,f66])).
% 0.21/0.50  fof(f532,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(X1,k2_struct_0(X0)) | ~v2_compts_1(sK3(X0,X1),X0) | v2_compts_1(X1,sK0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f525,f65])).
% 0.21/0.50  fof(f525,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,k2_struct_0(X0)) | ~v2_compts_1(sK3(X0,X1),X0) | v2_compts_1(X1,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f46,f38])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~v2_compts_1(sK3(X1,X2),X1) | v2_compts_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    r1_tarski(sK2,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f1053,plain,(
% 0.21/0.50    ~r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f1051,f56])).
% 0.21/0.50  fof(f1051,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f1050,f576])).
% 0.21/0.50  fof(f576,plain,(
% 0.21/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f67,f573])).
% 0.21/0.50  fof(f1050,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(resolution,[],[f1049,f80])).
% 0.21/0.50  fof(f1049,plain,(
% 0.21/0.50    ~m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f1048,f777])).
% 0.21/0.50  fof(f777,plain,(
% 0.21/0.50    v4_pre_topc(sK2,k1_pre_topc(sK0,k1_xboole_0)) | ~m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0)),
% 0.21/0.50    inference(forward_demodulation,[],[f635,f573])).
% 0.21/0.50  fof(f635,plain,(
% 0.21/0.50    ~m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0) | v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(backward_demodulation,[],[f273,f573])).
% 0.21/0.50  fof(f1048,plain,(
% 0.21/0.50    ~v4_pre_topc(sK2,k1_pre_topc(sK0,k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0)),
% 0.21/0.50    inference(resolution,[],[f894,f865])).
% 0.21/0.50  fof(f865,plain,(
% 0.21/0.50    ~v2_compts_1(sK2,k1_pre_topc(sK0,k1_xboole_0)) | ~m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0)),
% 0.21/0.50    inference(forward_demodulation,[],[f713,f573])).
% 0.21/0.50  fof(f713,plain,(
% 0.21/0.50    ~m1_pre_topc(k1_pre_topc(sK0,k1_xboole_0),sK0) | ~v2_compts_1(sK2,k1_pre_topc(sK0,sK1))),
% 0.21/0.50    inference(backward_demodulation,[],[f566,f573])).
% 0.21/0.50  fof(f894,plain,(
% 0.21/0.50    ( ! [X0] : (v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0)) | ~v4_pre_topc(X0,k1_pre_topc(sK0,k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f893,f582])).
% 0.21/0.50  fof(f582,plain,(
% 0.21/0.50    k1_xboole_0 = u1_struct_0(k1_pre_topc(sK0,k1_xboole_0))),
% 0.21/0.50    inference(backward_demodulation,[],[f108,f573])).
% 0.21/0.50  fof(f893,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,k1_xboole_0)))) | ~v4_pre_topc(X0,k1_pre_topc(sK0,k1_xboole_0)) | v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f892,f579])).
% 0.21/0.50  fof(f579,plain,(
% 0.21/0.50    l1_pre_topc(k1_pre_topc(sK0,k1_xboole_0))),
% 0.21/0.50    inference(backward_demodulation,[],[f85,f573])).
% 0.21/0.50  fof(f892,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,k1_xboole_0)))) | ~l1_pre_topc(k1_pre_topc(sK0,k1_xboole_0)) | ~v4_pre_topc(X0,k1_pre_topc(sK0,k1_xboole_0)) | v2_compts_1(X0,k1_pre_topc(sK0,k1_xboole_0))) )),
% 0.21/0.50    inference(resolution,[],[f721,f52])).
% 0.21/0.50  fof(f721,plain,(
% 0.21/0.50    v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f716,f576])).
% 0.21/0.50  fof(f716,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f128,f574])).
% 0.21/0.50  fof(f574,plain,(
% 0.21/0.50    v2_compts_1(k1_xboole_0,sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f32,f573])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | ~v2_compts_1(k1_xboole_0,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f124,f38])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0)) | ~v2_compts_1(k1_xboole_0,sK0)),
% 0.21/0.50    inference(superposition,[],[f59,f65])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_compts_1(k1_pre_topc(X0,k1_xboole_0)) | ~v2_compts_1(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X1 | v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (4741)------------------------------
% 0.21/0.50  % (4741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4741)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (4741)Memory used [KB]: 2174
% 0.21/0.50  % (4741)Time elapsed: 0.091 s
% 0.21/0.50  % (4741)------------------------------
% 0.21/0.50  % (4741)------------------------------
% 0.21/0.50  % (4728)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (4722)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (4720)Success in time 0.146 s
%------------------------------------------------------------------------------
