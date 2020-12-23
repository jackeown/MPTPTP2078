%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:10 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  110 (1118 expanded)
%              Number of leaves         :   11 ( 204 expanded)
%              Depth                    :   17
%              Number of atoms          :  292 (4061 expanded)
%              Number of equality atoms :   20 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f410,plain,(
    $false ),
    inference(subsumption_resolution,[],[f409,f57])).

fof(f57,plain,(
    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f56,f35])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
                & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
              & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tops_1)).

fof(f56,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f54,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f34,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f34,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f409,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f404,f341])).

fof(f341,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f32,f110,f307,f283,f313])).

fof(f313,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f303,f285])).

fof(f285,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(backward_demodulation,[],[f197,f273])).

fof(f273,plain,(
    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f271,f199])).

fof(f199,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f198,f123])).

fof(f123,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f114,f35])).

fof(f114,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f73,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f73,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f64,f35])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f198,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f187,f59])).

fof(f59,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f58,f35])).

fof(f58,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f55,f33])).

fof(f55,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f187,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(resolution,[],[f124,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X0)
      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f62,f35])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X0)
      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f33,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f124,plain,(
    m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f115,f35])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f73,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f271,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f265,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f265,plain,(
    r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f260,f75])).

fof(f75,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f66,f35])).

fof(f66,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f260,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f125,f33])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f116,f35])).

fof(f116,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f73,f38])).

fof(f197,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f186,f59])).

fof(f186,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(resolution,[],[f124,f74])).

fof(f74,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X1)
      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f65,f35])).

fof(f65,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X1)
      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f303,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(backward_demodulation,[],[f262,f273])).

fof(f262,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    inference(resolution,[],[f125,f105])).

fof(f105,plain,(
    m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f93,f35])).

fof(f93,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f70,f40])).

fof(f70,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f61,f35])).

fof(f61,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f33,f37])).

fof(f283,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(backward_demodulation,[],[f150,f273])).

fof(f150,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f79,f59])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r1_tarski(k1_tops_1(sK0,sK1),X0) ) ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f307,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f281,f273])).

fof(f281,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f135,f273])).

fof(f135,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f134,f72])).

fof(f72,plain,(
    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f63,f35])).

fof(f63,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f33,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f134,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1))))
    | v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f121,f35])).

fof(f121,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1))))
    | v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f73,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f110,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f109,f107])).

fof(f107,plain,(
    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f95,f35])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f70,f42])).

fof(f109,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f108,f69])).

fof(f69,plain,(
    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f60,f35])).

fof(f60,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f33,f36])).

fof(f108,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f96,f35])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(resolution,[],[f70,f45])).

fof(f32,plain,
    ( ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f404,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(resolution,[],[f175,f33])).

fof(f175,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X1))
      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X1) ) ),
    inference(forward_demodulation,[],[f174,f104])).

fof(f104,plain,(
    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f92,f35])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f70,f39])).

fof(f174,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X1)
      | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f162,f35])).

fof(f162,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X1)
      | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f105,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (25992)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.46  % (25984)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (25985)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (25975)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (25995)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (25987)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (25976)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (25977)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (25979)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (25973)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (25997)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (25996)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (25981)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (25986)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (25974)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (25982)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (25980)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (25978)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (25993)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (25988)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (25983)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.40/0.54  % (25994)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.40/0.54  % (25990)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.40/0.54  % (25989)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.40/0.55  % (25998)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.40/0.55  % (25991)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.56/0.56  % (25978)Refutation found. Thanks to Tanya!
% 1.56/0.56  % SZS status Theorem for theBenchmark
% 1.56/0.56  % SZS output start Proof for theBenchmark
% 1.56/0.56  fof(f410,plain,(
% 1.56/0.56    $false),
% 1.56/0.56    inference(subsumption_resolution,[],[f409,f57])).
% 1.56/0.56  fof(f57,plain,(
% 1.56/0.56    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)),
% 1.56/0.56    inference(subsumption_resolution,[],[f56,f35])).
% 1.56/0.56  fof(f35,plain,(
% 1.56/0.56    l1_pre_topc(sK0)),
% 1.56/0.56    inference(cnf_transformation,[],[f15])).
% 1.56/0.56  fof(f15,plain,(
% 1.56/0.56    ? [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.56/0.56    inference(flattening,[],[f14])).
% 1.56/0.56  fof(f14,plain,(
% 1.56/0.56    ? [X0] : (? [X1] : (((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.56/0.56    inference(ennf_transformation,[],[f13])).
% 1.56/0.56  fof(f13,negated_conjecture,(
% 1.56/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 1.56/0.56    inference(negated_conjecture,[],[f12])).
% 1.56/0.56  fof(f12,conjecture,(
% 1.56/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_tops_1)).
% 1.56/0.56  fof(f56,plain,(
% 1.56/0.56    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) | ~l1_pre_topc(sK0)),
% 1.56/0.56    inference(subsumption_resolution,[],[f54,f33])).
% 1.56/0.56  fof(f33,plain,(
% 1.56/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.56    inference(cnf_transformation,[],[f15])).
% 1.56/0.56  fof(f54,plain,(
% 1.56/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) | ~l1_pre_topc(sK0)),
% 1.56/0.56    inference(resolution,[],[f34,f43])).
% 1.56/0.56  fof(f43,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~l1_pre_topc(X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f29])).
% 1.56/0.56  fof(f29,plain,(
% 1.56/0.56    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.56/0.56    inference(ennf_transformation,[],[f7])).
% 1.56/0.56  fof(f7,axiom,(
% 1.56/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).
% 1.56/0.56  fof(f34,plain,(
% 1.56/0.56    v4_tops_1(sK1,sK0)),
% 1.56/0.56    inference(cnf_transformation,[],[f15])).
% 1.56/0.56  fof(f409,plain,(
% 1.56/0.56    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)),
% 1.56/0.56    inference(subsumption_resolution,[],[f404,f341])).
% 1.56/0.56  fof(f341,plain,(
% 1.56/0.56    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 1.56/0.56    inference(global_subsumption,[],[f32,f110,f307,f283,f313])).
% 1.56/0.56  fof(f313,plain,(
% 1.56/0.56    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))),
% 1.56/0.56    inference(subsumption_resolution,[],[f303,f285])).
% 1.56/0.56  fof(f285,plain,(
% 1.56/0.56    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.56/0.56    inference(backward_demodulation,[],[f197,f273])).
% 1.56/0.56  fof(f273,plain,(
% 1.56/0.56    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 1.56/0.56    inference(subsumption_resolution,[],[f271,f199])).
% 1.56/0.56  fof(f199,plain,(
% 1.56/0.56    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 1.56/0.56    inference(forward_demodulation,[],[f198,f123])).
% 1.56/0.56  fof(f123,plain,(
% 1.56/0.56    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 1.56/0.56    inference(subsumption_resolution,[],[f114,f35])).
% 1.56/0.56  fof(f114,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 1.56/0.56    inference(resolution,[],[f73,f36])).
% 1.56/0.56  fof(f36,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f17])).
% 1.56/0.56  fof(f17,plain,(
% 1.56/0.56    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.56/0.56    inference(flattening,[],[f16])).
% 1.56/0.56  fof(f16,plain,(
% 1.56/0.56    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f5])).
% 1.56/0.56  fof(f5,axiom,(
% 1.56/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 1.56/0.56  fof(f73,plain,(
% 1.56/0.56    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.56    inference(subsumption_resolution,[],[f64,f35])).
% 1.56/0.56  fof(f64,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.56    inference(resolution,[],[f33,f40])).
% 1.56/0.56  fof(f40,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f25])).
% 1.56/0.56  fof(f25,plain,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.56/0.56    inference(flattening,[],[f24])).
% 1.56/0.56  fof(f24,plain,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f8])).
% 1.56/0.56  fof(f8,axiom,(
% 1.56/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.56/0.56  fof(f198,plain,(
% 1.56/0.56    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))),
% 1.56/0.56    inference(subsumption_resolution,[],[f187,f59])).
% 1.56/0.56  fof(f59,plain,(
% 1.56/0.56    r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 1.56/0.56    inference(subsumption_resolution,[],[f58,f35])).
% 1.56/0.56  fof(f58,plain,(
% 1.56/0.56    r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 1.56/0.56    inference(subsumption_resolution,[],[f55,f33])).
% 1.56/0.56  fof(f55,plain,(
% 1.56/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 1.56/0.56    inference(resolution,[],[f34,f44])).
% 1.56/0.56  fof(f44,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~l1_pre_topc(X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f29])).
% 1.56/0.56  fof(f187,plain,(
% 1.56/0.56    ~r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))),
% 1.56/0.56    inference(resolution,[],[f124,f71])).
% 1.56/0.56  fof(f71,plain,(
% 1.56/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) )),
% 1.56/0.56    inference(subsumption_resolution,[],[f62,f35])).
% 1.56/0.56  fof(f62,plain,(
% 1.56/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) )),
% 1.56/0.56    inference(resolution,[],[f33,f38])).
% 1.56/0.56  fof(f38,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f21])).
% 1.56/0.56  fof(f21,plain,(
% 1.56/0.56    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.56/0.56    inference(flattening,[],[f20])).
% 1.56/0.56  fof(f20,plain,(
% 1.56/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.56/0.56    inference(ennf_transformation,[],[f6])).
% 1.56/0.56  fof(f6,axiom,(
% 1.56/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 1.56/0.56  fof(f124,plain,(
% 1.56/0.56    m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.56    inference(subsumption_resolution,[],[f115,f35])).
% 1.56/0.56  fof(f115,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.56    inference(resolution,[],[f73,f37])).
% 1.56/0.56  fof(f37,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f19])).
% 1.56/0.56  fof(f19,plain,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.56/0.56    inference(flattening,[],[f18])).
% 1.56/0.56  fof(f18,plain,(
% 1.56/0.56    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f4])).
% 1.56/0.56  fof(f4,axiom,(
% 1.56/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.56/0.56  fof(f271,plain,(
% 1.56/0.56    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 1.56/0.56    inference(resolution,[],[f265,f50])).
% 1.56/0.56  fof(f50,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.56/0.56    inference(cnf_transformation,[],[f1])).
% 1.56/0.56  fof(f1,axiom,(
% 1.56/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.56  fof(f265,plain,(
% 1.56/0.56    r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))),
% 1.56/0.56    inference(subsumption_resolution,[],[f260,f75])).
% 1.56/0.56  fof(f75,plain,(
% 1.56/0.56    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.56/0.56    inference(subsumption_resolution,[],[f66,f35])).
% 1.56/0.56  fof(f66,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.56/0.56    inference(resolution,[],[f33,f42])).
% 1.56/0.56  fof(f42,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f28])).
% 1.56/0.56  fof(f28,plain,(
% 1.56/0.56    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.56/0.56    inference(ennf_transformation,[],[f10])).
% 1.56/0.56  fof(f10,axiom,(
% 1.56/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.56/0.56  fof(f260,plain,(
% 1.56/0.56    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))),
% 1.56/0.56    inference(resolution,[],[f125,f33])).
% 1.56/0.56  fof(f125,plain,(
% 1.56/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,sK1),X0) | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0))) )),
% 1.56/0.56    inference(subsumption_resolution,[],[f116,f35])).
% 1.56/0.56  fof(f116,plain,(
% 1.56/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,sK1),X0) | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0))) )),
% 1.56/0.56    inference(resolution,[],[f73,f38])).
% 1.56/0.56  fof(f197,plain,(
% 1.56/0.56    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))),
% 1.56/0.56    inference(subsumption_resolution,[],[f186,f59])).
% 1.56/0.56  fof(f186,plain,(
% 1.56/0.56    ~r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))),
% 1.56/0.56    inference(resolution,[],[f124,f74])).
% 1.56/0.56  fof(f74,plain,(
% 1.56/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X1) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X1))) )),
% 1.56/0.56    inference(subsumption_resolution,[],[f65,f35])).
% 1.56/0.56  fof(f65,plain,(
% 1.56/0.56    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X1) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X1))) )),
% 1.56/0.56    inference(resolution,[],[f33,f41])).
% 1.56/0.56  fof(f41,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f27])).
% 1.56/0.56  fof(f27,plain,(
% 1.56/0.56    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.56/0.56    inference(flattening,[],[f26])).
% 1.56/0.56  fof(f26,plain,(
% 1.56/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.56/0.56    inference(ennf_transformation,[],[f11])).
% 1.56/0.56  fof(f11,axiom,(
% 1.56/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.56/0.56  fof(f303,plain,(
% 1.56/0.56    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) | ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.56/0.56    inference(backward_demodulation,[],[f262,f273])).
% 1.56/0.56  fof(f262,plain,(
% 1.56/0.56    ~r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))),
% 1.56/0.56    inference(resolution,[],[f125,f105])).
% 1.56/0.56  fof(f105,plain,(
% 1.56/0.56    m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.56    inference(subsumption_resolution,[],[f93,f35])).
% 1.56/0.56  fof(f93,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.56    inference(resolution,[],[f70,f40])).
% 1.56/0.56  fof(f70,plain,(
% 1.56/0.56    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.56    inference(subsumption_resolution,[],[f61,f35])).
% 1.56/0.56  fof(f61,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.56/0.56    inference(resolution,[],[f33,f37])).
% 1.56/0.56  fof(f283,plain,(
% 1.56/0.56    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 1.56/0.56    inference(backward_demodulation,[],[f150,f273])).
% 1.56/0.56  fof(f150,plain,(
% 1.56/0.56    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 1.56/0.56    inference(resolution,[],[f79,f59])).
% 1.56/0.56  fof(f79,plain,(
% 1.56/0.56    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) )),
% 1.56/0.56    inference(resolution,[],[f75,f51])).
% 1.56/0.56  fof(f51,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f31])).
% 1.56/0.56  fof(f31,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.56/0.56    inference(flattening,[],[f30])).
% 1.56/0.56  fof(f30,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.56/0.56    inference(ennf_transformation,[],[f2])).
% 1.56/0.56  fof(f2,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.56/0.56  fof(f307,plain,(
% 1.56/0.56    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | v4_tops_1(k1_tops_1(sK0,sK1),sK0)),
% 1.56/0.56    inference(forward_demodulation,[],[f281,f273])).
% 1.56/0.56  fof(f281,plain,(
% 1.56/0.56    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | v4_tops_1(k1_tops_1(sK0,sK1),sK0)),
% 1.56/0.56    inference(backward_demodulation,[],[f135,f273])).
% 1.56/0.56  fof(f135,plain,(
% 1.56/0.56    ~r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) | v4_tops_1(k1_tops_1(sK0,sK1),sK0)),
% 1.56/0.56    inference(forward_demodulation,[],[f134,f72])).
% 1.56/0.56  fof(f72,plain,(
% 1.56/0.56    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 1.56/0.56    inference(subsumption_resolution,[],[f63,f35])).
% 1.56/0.56  fof(f63,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 1.56/0.56    inference(resolution,[],[f33,f39])).
% 1.56/0.56  fof(f39,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f23])).
% 1.56/0.56  fof(f23,plain,(
% 1.56/0.56    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.56/0.56    inference(flattening,[],[f22])).
% 1.56/0.56  fof(f22,plain,(
% 1.56/0.56    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.56/0.56    inference(ennf_transformation,[],[f9])).
% 1.56/0.56  fof(f9,axiom,(
% 1.56/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 1.56/0.56  fof(f134,plain,(
% 1.56/0.56    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) | ~r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) | v4_tops_1(k1_tops_1(sK0,sK1),sK0)),
% 1.56/0.56    inference(subsumption_resolution,[],[f121,f35])).
% 1.56/0.56  fof(f121,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) | ~r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) | v4_tops_1(k1_tops_1(sK0,sK1),sK0)),
% 1.56/0.56    inference(resolution,[],[f73,f45])).
% 1.56/0.56  fof(f45,plain,(
% 1.56/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f29])).
% 1.56/0.56  fof(f110,plain,(
% 1.56/0.56    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) | v4_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 1.56/0.56    inference(subsumption_resolution,[],[f109,f107])).
% 1.56/0.56  fof(f107,plain,(
% 1.56/0.56    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))),
% 1.56/0.56    inference(subsumption_resolution,[],[f95,f35])).
% 1.56/0.56  fof(f95,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))),
% 1.56/0.56    inference(resolution,[],[f70,f42])).
% 1.56/0.56  fof(f109,plain,(
% 1.56/0.56    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) | v4_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 1.56/0.56    inference(forward_demodulation,[],[f108,f69])).
% 1.56/0.56  fof(f69,plain,(
% 1.56/0.56    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),
% 1.56/0.56    inference(subsumption_resolution,[],[f60,f35])).
% 1.56/0.56  fof(f60,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),
% 1.56/0.56    inference(resolution,[],[f33,f36])).
% 1.56/0.56  fof(f108,plain,(
% 1.56/0.56    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) | v4_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 1.56/0.56    inference(subsumption_resolution,[],[f96,f35])).
% 1.56/0.56  fof(f96,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) | ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) | v4_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 1.56/0.56    inference(resolution,[],[f70,f45])).
% 1.56/0.56  fof(f32,plain,(
% 1.56/0.56    ~v4_tops_1(k1_tops_1(sK0,sK1),sK0) | ~v4_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 1.56/0.56    inference(cnf_transformation,[],[f15])).
% 1.56/0.56  fof(f404,plain,(
% 1.56/0.56    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)),
% 1.56/0.56    inference(resolution,[],[f175,f33])).
% 1.56/0.56  fof(f175,plain,(
% 1.56/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X1)) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X1)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f174,f104])).
% 1.56/0.56  fof(f104,plain,(
% 1.56/0.56    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.56/0.56    inference(subsumption_resolution,[],[f92,f35])).
% 1.56/0.56  fof(f92,plain,(
% 1.56/0.56    ~l1_pre_topc(sK0) | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.56/0.56    inference(resolution,[],[f70,f39])).
% 1.56/0.56  fof(f174,plain,(
% 1.56/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X1) | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,X1))) )),
% 1.56/0.56    inference(subsumption_resolution,[],[f162,f35])).
% 1.56/0.56  fof(f162,plain,(
% 1.56/0.56    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X1) | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_tops_1(sK0,X1))) )),
% 1.56/0.56    inference(resolution,[],[f105,f41])).
% 1.56/0.56  % SZS output end Proof for theBenchmark
% 1.56/0.56  % (25978)------------------------------
% 1.56/0.56  % (25978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (25978)Termination reason: Refutation
% 1.56/0.56  
% 1.56/0.56  % (25978)Memory used [KB]: 6268
% 1.56/0.56  % (25978)Time elapsed: 0.157 s
% 1.56/0.56  % (25978)------------------------------
% 1.56/0.56  % (25978)------------------------------
% 1.56/0.56  % (25972)Success in time 0.201 s
%------------------------------------------------------------------------------
