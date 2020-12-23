%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 951 expanded)
%              Number of leaves         :   12 ( 168 expanded)
%              Depth                    :   29
%              Number of atoms          :  386 (4377 expanded)
%              Number of equality atoms :   69 ( 738 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(subsumption_resolution,[],[f330,f303])).

fof(f303,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f297])).

fof(f297,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f33,f284])).

fof(f284,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f109,f280])).

fof(f280,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f279,f157])).

fof(f157,plain,
    ( ~ r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f88,f40])).

fof(f40,plain,(
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

fof(f88,plain,(
    r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f87,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f87,plain,
    ( v2_struct_0(sK0)
    | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f86,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f69,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f34,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_tmap_1)).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f279,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f278,f37])).

fof(f278,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f275,f116])).

fof(f116,plain,(
    m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f115,f76])).

fof(f76,plain,(
    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f75,f35])).

fof(f75,plain,
    ( v2_struct_0(sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f74,f37])).

fof(f74,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f65,f36])).

fof(f65,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f115,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f113,f73])).

fof(f73,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f72,f35])).

fof(f72,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f71,f37])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f64,f36])).

fof(f64,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f113,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(resolution,[],[f85,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f85,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f84,f35])).

fof(f84,plain,
    ( v2_struct_0(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f83,f37])).

fof(f83,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f68,f36])).

fof(f68,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f34,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f275,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f274,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f274,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f272,f116])).

fof(f272,plain,
    ( ~ m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f220,f114])).

fof(f114,plain,(
    v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f112,f76])).

fof(f112,plain,(
    v1_tops_2(u1_pre_topc(k6_tmap_1(sK0,sK1)),k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f85,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v1_tops_2(u1_pre_topc(X0),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_2(u1_pre_topc(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).

fof(f220,plain,(
    ! [X1] :
      ( ~ v1_tops_2(X1,k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | v1_tops_2(X1,sK0)
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ) ),
    inference(forward_demodulation,[],[f219,f73])).

fof(f219,plain,(
    ! [X1] :
      ( ~ v1_tops_2(X1,k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | v1_tops_2(X1,sK0)
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f218,f35])).

fof(f218,plain,(
    ! [X1] :
      ( ~ v1_tops_2(X1,k6_tmap_1(sK0,sK1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | v1_tops_2(X1,sK0)
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f217,f37])).

fof(f217,plain,(
    ! [X1] :
      ( ~ v1_tops_2(X1,k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | v1_tops_2(X1,sK0)
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f212,f36])).

fof(f212,plain,(
    ! [X1] :
      ( ~ v1_tops_2(X1,k6_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | v1_tops_2(X1,sK0)
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ) ),
    inference(superposition,[],[f47,f199])).

fof(f199,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f198,f35])).

fof(f198,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f197,f34])).

fof(f197,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f196,f37])).

fof(f196,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f194,f36])).

fof(f194,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f105,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f105,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f104,f37])).

fof(f104,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f103,f34])).

fof(f103,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f32,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f32,plain,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

% (15164)Refutation not found, incomplete strategy% (15164)------------------------------
% (15164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15164)Termination reason: Refutation not found, incomplete strategy

% (15164)Memory used [KB]: 10618
% (15164)Time elapsed: 0.063 s
% (15164)------------------------------
% (15164)------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

fof(f109,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f108,f73])).

fof(f108,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f107,f76])).

fof(f107,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f106,f85])).

fof(f106,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f79,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f79,plain,(
    v1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f78,f35])).

fof(f78,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f77,f37])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f66,f36])).

fof(f66,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f34,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f330,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f329,f37])).

fof(f329,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f328,f34])).

fof(f328,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f296,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f296,plain,(
    r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f91,f280])).

fof(f91,plain,
    ( u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f90,f35])).

fof(f90,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f89,f37])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f70,f36])).

fof(f70,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(resolution,[],[f34,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:16:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (15158)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (15166)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (15163)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (15158)Refutation not found, incomplete strategy% (15158)------------------------------
% 0.21/0.50  % (15158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15161)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (15167)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (15162)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (15158)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15158)Memory used [KB]: 10618
% 0.21/0.51  % (15158)Time elapsed: 0.082 s
% 0.21/0.51  % (15158)------------------------------
% 0.21/0.51  % (15158)------------------------------
% 0.21/0.51  % (15180)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (15165)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (15171)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (15171)Refutation not found, incomplete strategy% (15171)------------------------------
% 0.21/0.51  % (15171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15171)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15171)Memory used [KB]: 6268
% 0.21/0.51  % (15171)Time elapsed: 0.096 s
% 0.21/0.51  % (15171)------------------------------
% 0.21/0.51  % (15171)------------------------------
% 0.21/0.51  % (15170)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (15164)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (15165)Refutation not found, incomplete strategy% (15165)------------------------------
% 0.21/0.51  % (15165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15165)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15165)Memory used [KB]: 1663
% 0.21/0.51  % (15165)Time elapsed: 0.094 s
% 0.21/0.51  % (15165)------------------------------
% 0.21/0.51  % (15165)------------------------------
% 0.21/0.51  % (15163)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f330,f303])).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    ~v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f297])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f33,f284])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.21/0.51    inference(backward_demodulation,[],[f109,f280])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f279,f157])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ~r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f88,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    v2_struct_0(sK0) | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f34,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_tmap_1)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f278,f37])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f275,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    inference(forward_demodulation,[],[f115,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f75,f35])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    v2_struct_0(sK0) | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f74,f37])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f65,f36])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k5_tmap_1(sK0,sK1) = u1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f34,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    inference(forward_demodulation,[],[f113,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f72,f35])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f37])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f64,f36])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f34,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 0.21/0.51    inference(resolution,[],[f85,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f84,f35])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    v2_struct_0(sK0) | l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f83,f37])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f68,f36])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f34,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(resolution,[],[f274,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r1_tarski(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    v1_tops_2(k5_tmap_1(sK0,sK1),sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f272,f116])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    ~m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k5_tmap_1(sK0,sK1),sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f220,f114])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(forward_demodulation,[],[f112,f76])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    v1_tops_2(u1_pre_topc(k6_tmap_1(sK0,sK1)),k6_tmap_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f85,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | v1_tops_2(u1_pre_topc(X0),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => v1_tops_2(u1_pre_topc(X0),X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_tops_2(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X1,sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f219,f73])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_tops_2(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) | v1_tops_2(X1,sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f218,f35])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_tops_2(X1,k6_tmap_1(sK0,sK1)) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) | v1_tops_2(X1,sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f217,f37])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_tops_2(X1,k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) | v1_tops_2(X1,sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f212,f36])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_tops_2(X1,k6_tmap_1(sK0,sK1)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) | v1_tops_2(X1,sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)) )),
% 0.21/0.51    inference(superposition,[],[f47,f199])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f198,f35])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f197,f34])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f196,f37])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f194,f36])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f105,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    r2_hidden(sK1,u1_pre_topc(sK0)) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f104,f37])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | r2_hidden(sK1,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f103,f34])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.51    inference(resolution,[],[f32,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    v3_pre_topc(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | v1_tops_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  % (15164)Refutation not found, incomplete strategy% (15164)------------------------------
% 0.21/0.52  % (15164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15164)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15164)Memory used [KB]: 10618
% 0.21/0.52  % (15164)Time elapsed: 0.063 s
% 0.21/0.52  % (15164)------------------------------
% 0.21/0.52  % (15164)------------------------------
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.21/0.52    inference(forward_demodulation,[],[f108,f73])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1))),
% 0.21/0.52    inference(forward_demodulation,[],[f107,f76])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f106,f85])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 0.21/0.52    inference(resolution,[],[f79,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    v1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f35])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    v2_struct_0(sK0) | v1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f77,f37])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f66,f36])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.21/0.52    inference(resolution,[],[f34,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ~v3_pre_topc(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f330,plain,(
% 0.21/0.52    v3_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f329,f37])).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | v3_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f328,f34])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(sK1,sK0)),
% 0.21/0.52    inference(resolution,[],[f296,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f296,plain,(
% 0.21/0.52    r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f283])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    u1_pre_topc(sK0) != u1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.21/0.52    inference(backward_demodulation,[],[f91,f280])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f90,f35])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f89,f37])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.21/0.52    inference(subsumption_resolution,[],[f70,f36])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK1) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.21/0.52    inference(resolution,[],[f34,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (15163)------------------------------
% 0.21/0.52  % (15163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15163)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (15163)Memory used [KB]: 6268
% 0.21/0.52  % (15163)Time elapsed: 0.093 s
% 0.21/0.52  % (15163)------------------------------
% 0.21/0.52  % (15163)------------------------------
% 0.21/0.52  % (15157)Success in time 0.154 s
%------------------------------------------------------------------------------
