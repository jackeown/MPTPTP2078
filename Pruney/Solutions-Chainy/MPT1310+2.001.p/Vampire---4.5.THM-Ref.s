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
% DateTime   : Thu Dec  3 13:13:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 269 expanded)
%              Number of leaves         :   15 (  83 expanded)
%              Depth                    :   19
%              Number of atoms          :  263 (1366 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(subsumption_resolution,[],[f200,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f200,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f178,f43])).

fof(f43,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f178,plain,(
    ~ v1_xboole_0(k3_tarski(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f96,f165])).

fof(f165,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f164,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)
    & v1_finset_1(sK1)
    & v2_tops_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
            & v1_finset_1(X1)
            & v2_tops_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),X1),sK0)
          & v1_finset_1(X1)
          & v2_tops_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),X1),sK0)
        & v1_finset_1(X1)
        & v2_tops_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)
      & v1_finset_1(sK1)
      & v2_tops_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_finset_1(X1)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_finset_1(X1)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( ( v1_finset_1(X1)
                & v2_tops_2(X1,X0) )
             => v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ( v1_finset_1(X1)
              & v2_tops_2(X1,X0) )
           => v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tops_2)).

fof(f164,plain,
    ( ~ v2_pre_topc(sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f163,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f162,f79])).

fof(f79,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f38,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f162,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f161,f72])).

fof(f72,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f71,f37])).

fof(f71,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f70,f38])).

fof(f70,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f39,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

fof(f39,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f161,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f160,f86])).

fof(f86,plain,(
    v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f85,f61])).

fof(f61,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f85,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f77,f40])).

fof(f40,plain,(
    v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ v1_finset_1(sK1)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f38,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
      | ~ v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
              | ~ v1_finset_1(X1) )
            & ( v1_finset_1(X1)
              | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tops_2)).

fof(f160,plain,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f155,f98])).

fof(f98,plain,(
    ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f97,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f93,f87])).

fof(f87,plain,(
    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f80,f81])).

fof(f81,plain,(
    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(resolution,[],[f38,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f80,plain,(
    m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f38,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f93,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f89,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f89,plain,(
    ~ v4_pre_topc(k3_tarski(sK1),sK0) ),
    inference(backward_demodulation,[],[f41,f81])).

fof(f41,plain,(
    ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f155,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f52,f88])).

fof(f88,plain,
    ( k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f78,f81])).

fof(f78,plain,
    ( k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f38,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

fof(f52,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v1_finset_1(X1)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_finset_1(X1)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_finset_1(X1)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ( v1_finset_1(X1)
              & v1_tops_2(X1,X0) )
           => v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_2)).

fof(f96,plain,(
    ~ v1_xboole_0(k3_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f95,f36])).

fof(f95,plain,
    ( ~ v1_xboole_0(k3_tarski(sK1))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f94,f37])).

fof(f94,plain,
    ( ~ v1_xboole_0(k3_tarski(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f92,f87])).

fof(f92,plain,
    ( ~ v1_xboole_0(k3_tarski(sK1))
    | ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f89,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:08:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (5838)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.48  % (5854)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.48  % (5834)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (5843)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (5843)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f200,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(forward_demodulation,[],[f178,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    ~v1_xboole_0(k3_tarski(k1_xboole_0))),
% 0.21/0.50    inference(backward_demodulation,[],[f96,f165])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f164,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    (~v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) & v1_finset_1(sK1) & v2_tops_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f31,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (~v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) & v1_finset_1(X1) & v2_tops_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),X1),sK0) & v1_finset_1(X1) & v2_tops_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X1] : (~v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),X1),sK0) & v1_finset_1(X1) & v2_tops_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) & v1_finset_1(sK1) & v2_tops_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (~v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) & v1_finset_1(X1) & v2_tops_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((~v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) & (v1_finset_1(X1) & v2_tops_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_finset_1(X1) & v2_tops_2(X1,X0)) => v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_finset_1(X1) & v2_tops_2(X1,X0)) => v4_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tops_2)).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f163,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f162,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    inference(resolution,[],[f38,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f161,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f71,f37])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f70,f38])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f39,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) & (v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    v2_tops_2(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f160,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f85,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    l1_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f37,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) | ~l1_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f77,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    v1_finset_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) | ~v1_finset_1(sK1) | ~l1_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f38,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) | ~v1_finset_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) | ~v1_finset_1(X1)) & (v1_finset_1(X1) | ~v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) <=> v1_finset_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) <=> v1_finset_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tops_2)).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ~v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) | ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k1_xboole_0 = sK1),
% 0.21/0.50    inference(subsumption_resolution,[],[f155,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f97,f37])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f93,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f80,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1)),
% 0.21/0.50    inference(resolution,[],[f38,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_setfam_1(X0,X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (k5_setfam_1(X0,X1) = k3_tarski(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k5_setfam_1(X0,X1) = k3_tarski(X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(resolution,[],[f38,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0) | ~m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(resolution,[],[f89,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ~v4_pre_topc(k3_tarski(sK1),sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f41,f81])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ~v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0) | ~v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) | ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(superposition,[],[f52,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(backward_demodulation,[],[f78,f81])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1)) | k1_xboole_0 = sK1),
% 0.21/0.51    inference(resolution,[],[f38,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : (k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : ((k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_finset_1(X1) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_finset_1(X1) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | (~v1_finset_1(X1) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_finset_1(X1) & v1_tops_2(X1,X0)) => v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_2)).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ~v1_xboole_0(k3_tarski(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f95,f36])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ~v1_xboole_0(k3_tarski(sK1)) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f94,f37])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~v1_xboole_0(k3_tarski(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f92,f87])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~v1_xboole_0(k3_tarski(sK1)) | ~m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.51    inference(resolution,[],[f89,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (5843)------------------------------
% 0.21/0.51  % (5843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5843)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (5843)Memory used [KB]: 1663
% 0.21/0.51  % (5843)Time elapsed: 0.090 s
% 0.21/0.51  % (5843)------------------------------
% 0.21/0.51  % (5843)------------------------------
% 0.21/0.51  % (5831)Success in time 0.146 s
%------------------------------------------------------------------------------
