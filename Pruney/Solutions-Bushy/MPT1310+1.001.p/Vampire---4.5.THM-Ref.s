%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1310+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:42 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 465 expanded)
%              Number of leaves         :   15 ( 143 expanded)
%              Depth                    :   23
%              Number of atoms          :  278 (2396 expanded)
%              Number of equality atoms :   28 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(resolution,[],[f283,f36])).

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

fof(f283,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f282,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f282,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f272,f232])).

fof(f232,plain,(
    ~ v4_pre_topc(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f166,f43])).

fof(f43,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f166,plain,(
    ~ v4_pre_topc(k3_tarski(k1_xboole_0),sK0) ),
    inference(backward_demodulation,[],[f58,f161])).

fof(f161,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f160,f37])).

fof(f160,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f159,f58])).

fof(f159,plain,
    ( v4_pre_topc(k3_tarski(sK1),sK0)
    | k1_xboole_0 = sK1
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f158,f60])).

fof(f60,plain,(
    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f59,f57])).

fof(f57,plain,(
    k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(resolution,[],[f53,f38])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f59,plain,(
    m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f54,f38])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f158,plain,
    ( ~ m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = sK1
    | v4_pre_topc(k3_tarski(sK1),sK0) ),
    inference(resolution,[],[f157,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f48,f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f157,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | k1_xboole_0 = sK1
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f156,f61])).

fof(f61,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f55,f38])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f156,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK1
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f155,f38])).

fof(f155,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f153,f78])).

fof(f78,plain,(
    v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f77,f37])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f76,f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f76,plain,
    ( ~ l1_struct_0(sK0)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f75,f38])).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v1_finset_1(k7_setfam_1(u1_struct_0(X0),sK1))
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f45,f40])).

fof(f40,plain,(
    v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(X1)
      | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tops_2)).

fof(f153,plain,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f123,f39])).

fof(f39,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f123,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f120,f49])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

fof(f120,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1)),sK0)
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f119,f101])).

fof(f101,plain,
    ( k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_tarski(sK1))
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f96,f57])).

fof(f96,plain,
    ( k1_xboole_0 = sK1
    | k6_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f56,f38])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ),
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

fof(f119,plain,(
    ! [X0] :
      ( v3_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(X0,sK0)
      | ~ v1_finset_1(X0) ) ),
    inference(resolution,[],[f118,f36])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ v1_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v3_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0)
      | ~ v1_finset_1(X0) ) ),
    inference(resolution,[],[f52,f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_finset_1(X1)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ( v1_finset_1(X1)
              & v1_tops_2(X1,X0) )
           => v3_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_2)).

fof(f58,plain,(
    ~ v4_pre_topc(k3_tarski(sK1),sK0) ),
    inference(backward_demodulation,[],[f41,f57])).

fof(f41,plain,(
    ~ v4_pre_topc(k5_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f272,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f233,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f51,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0)
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f233,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f167,f43])).

fof(f167,plain,(
    m1_subset_1(k3_tarski(k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f60,f161])).

%------------------------------------------------------------------------------
