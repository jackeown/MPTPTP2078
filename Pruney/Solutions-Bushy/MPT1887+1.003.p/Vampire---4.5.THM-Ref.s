%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1887+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:51 EST 2020

% Result     : Theorem 8.63s
% Output     : Refutation 8.63s
% Verified   : 
% Statistics : Number of formulae       :  135 (1026 expanded)
%              Number of leaves         :   22 ( 235 expanded)
%              Depth                    :   25
%              Number of atoms          :  313 (4064 expanded)
%              Number of equality atoms :   36 ( 431 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20320,plain,(
    $false ),
    inference(subsumption_resolution,[],[f20122,f148])).

fof(f148,plain,(
    ! [X0] : ~ r1_tarski(k1_tarski(X0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f143,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f143,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f59,f96,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f96,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f90,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f20122,plain,(
    r1_tarski(k1_tarski(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f214,f20120])).

fof(f20120,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f18387,f20119])).

fof(f20119,plain,(
    k1_xboole_0 = k3_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(unit_resulting_resolution,[],[f20116,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f20116,plain,(
    r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(unit_resulting_resolution,[],[f58,f56,f2454,f115,f316,f20051,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_xboole_0(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X1,X0)
                  & r1_xboole_0(X1,X2) )
               => r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

fof(f20051,plain,(
    r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2)) ),
    inference(unit_resulting_resolution,[],[f20046,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f81,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f20046,plain,(
    k1_xboole_0 = k3_xboole_0(k1_tarski(sK2),k2_pre_topc(sK0,k1_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f20045,f82])).

fof(f20045,plain,(
    r1_xboole_0(k1_tarski(sK2),k2_pre_topc(sK0,k1_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f20041,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f20041,plain,(
    ~ r2_hidden(sK2,k2_pre_topc(sK0,k1_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f20040,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f20040,plain,(
    ~ r1_tarski(k1_tarski(sK2),k2_pre_topc(sK0,k1_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f58,f115,f296,f316,f18386,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_pre_topc(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(f18386,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k1_tarski(sK2)),k2_pre_topc(sK0,k1_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f174,f3647,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f3647,plain,(
    r1_tarski(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f3646,f210])).

fof(f210,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(unit_resulting_resolution,[],[f178,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f178,plain,(
    r1_tarski(k1_tarski(sK1),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(backward_demodulation,[],[f100,f170])).

fof(f170,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    inference(unit_resulting_resolution,[],[f51,f93,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f93,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f55,f92,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f92,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f58,f61])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                 => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

fof(f51,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,(
    r1_tarski(k1_tarski(sK1),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(unit_resulting_resolution,[],[f52,f83])).

fof(f52,plain,(
    r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f3646,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(k1_tarski(sK1),k2_pre_topc(sK0,k1_tarski(sK2)))),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f3566,f71])).

fof(f3566,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(k2_pre_topc(sK0,k1_tarski(sK2)),k1_tarski(sK1))),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(unit_resulting_resolution,[],[f58,f244,f289,f295,f315,f63])).

fof(f315,plain,(
    m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f58,f115,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f295,plain,(
    v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f58,f56,f115,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f289,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f249,f71])).

fof(f249,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(backward_demodulation,[],[f221,f237])).

fof(f237,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k9_subset_1(X1,X0,X1) ),
    inference(unit_resulting_resolution,[],[f96,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f221,plain,(
    ! [X0,X1] : r1_tarski(k9_subset_1(X0,X1,X0),X0) ),
    inference(unit_resulting_resolution,[],[f203,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f203,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(X0,X1,X0),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f96,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f244,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f205,f239])).

fof(f239,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k1_tarski(sK1)) = k3_xboole_0(X0,k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f118,f88])).

fof(f118,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f108,f85])).

fof(f108,plain,(
    r1_tarski(k1_tarski(sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f105,f83])).

fof(f105,plain,(
    r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f54,f93,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f54,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f205,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f118,f87])).

fof(f174,plain,(
    k2_pre_topc(sK0,k1_tarski(sK1)) != k2_pre_topc(sK0,k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f173,f170])).

fof(f173,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f53,f171])).

fof(f171,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(unit_resulting_resolution,[],[f54,f93,f75])).

fof(f53,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f296,plain,(
    v4_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f58,f56,f118,f76])).

fof(f316,plain,(
    m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f58,f118,f77])).

fof(f115,plain,(
    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f107,f85])).

fof(f107,plain,(
    r1_tarski(k1_tarski(sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f104,f83])).

fof(f104,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f51,f93,f74])).

fof(f2454,plain,(
    v3_pre_topc(k2_pre_topc(sK0,k1_tarski(sK1)),sK0) ),
    inference(superposition,[],[f2303,f117])).

fof(f117,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f108,f73])).

fof(f2303,plain,(
    ! [X0] : v3_pre_topc(k2_pre_topc(sK0,k3_xboole_0(X0,u1_struct_0(sK0))),sK0) ),
    inference(unit_resulting_resolution,[],[f56,f57,f58,f337,f336,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f336,plain,(
    ! [X0] : m1_subset_1(k2_pre_topc(sK0,k3_xboole_0(X0,u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f58,f250,f77])).

fof(f250,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X1,X0),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f203,f237])).

fof(f337,plain,(
    ! [X0] : v4_pre_topc(k2_pre_topc(sK0,k3_xboole_0(X0,u1_struct_0(sK0))),sK0) ),
    inference(unit_resulting_resolution,[],[f58,f56,f250,f76])).

fof(f57,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f18387,plain,(
    k2_pre_topc(sK0,k1_tarski(sK1)) = k3_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(unit_resulting_resolution,[],[f3647,f73])).

fof(f214,plain,(
    r1_tarski(k1_tarski(sK1),k2_pre_topc(sK0,k1_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f58,f118,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

%------------------------------------------------------------------------------
