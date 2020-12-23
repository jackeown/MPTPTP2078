%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1638+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 (1627 expanded)
%              Number of leaves         :    9 ( 298 expanded)
%              Depth                    :   21
%              Number of atoms          :  291 (6328 expanded)
%              Number of equality atoms :   41 ( 295 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f299,plain,(
    $false ),
    inference(global_subsumption,[],[f35,f127,f298])).

fof(f298,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f297,f271])).

fof(f271,plain,(
    sK1 = sK4(sK2,sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f267,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f267,plain,(
    r2_hidden(sK4(sK2,sK0,k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(resolution,[],[f205,f127])).

fof(f205,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k6_waybel_0(sK0,sK1))
      | r2_hidden(sK4(X2,sK0,k1_tarski(sK1)),k1_tarski(sK1)) ) ),
    inference(subsumption_resolution,[],[f204,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k6_waybel_0(X0,X1))
                <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_0)).

fof(f204,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k6_waybel_0(sK0,sK1))
      | r2_hidden(sK4(X2,sK0,k1_tarski(sK1)),k1_tarski(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f203,f91])).

fof(f91,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f90,f88])).

fof(f88,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f82,f67])).

fof(f67,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f66,f38])).

fof(f66,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f65,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f65,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f39,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f39,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f83,f67])).

fof(f83,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f203,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k6_waybel_0(sK0,sK1))
      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(X2,sK0,k1_tarski(sK1)),k1_tarski(sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f194,f39])).

fof(f194,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k6_waybel_0(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(X2,sK0,k1_tarski(sK1)),k1_tarski(sK1))
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f43,f110])).

fof(f110,plain,(
    k6_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f109,f89])).

fof(f89,plain,(
    k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k1_tarski(sK1)) ),
    inference(backward_demodulation,[],[f85,f88])).

fof(f85,plain,(
    k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f84,f38])).

fof(f84,plain,
    ( v2_struct_0(sK0)
    | k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f80,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f37,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_0)).

fof(f109,plain,(
    k4_waybel_0(sK0,k1_tarski(sK1)) = a_2_1_waybel_0(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f108,f38])).

fof(f108,plain,
    ( v2_struct_0(sK0)
    | k4_waybel_0(sK0,k1_tarski(sK1)) = a_2_1_waybel_0(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f104,f39])).

fof(f104,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k4_waybel_0(sK0,k1_tarski(sK1)) = a_2_1_waybel_0(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f91,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_waybel_0)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK4(X0,X1,X2),X2)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_waybel_0)).

fof(f297,plain,(
    r1_orders_2(sK0,sK4(sK2,sK0,k1_tarski(sK1)),sK2) ),
    inference(forward_demodulation,[],[f295,f218])).

fof(f218,plain,(
    sK2 = sK3(sK2,sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f211,f127])).

fof(f211,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k6_waybel_0(sK0,sK1))
      | sK3(X4,sK0,k1_tarski(sK1)) = X4 ) ),
    inference(subsumption_resolution,[],[f210,f38])).

fof(f210,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k6_waybel_0(sK0,sK1))
      | sK3(X4,sK0,k1_tarski(sK1)) = X4
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f209,f91])).

fof(f209,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k6_waybel_0(sK0,sK1))
      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X4,sK0,k1_tarski(sK1)) = X4
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f196,f39])).

fof(f196,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k6_waybel_0(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X4,sK0,k1_tarski(sK1)) = X4
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f45,f110])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK3(X0,X1,X2) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f295,plain,(
    r1_orders_2(sK0,sK4(sK2,sK0,k1_tarski(sK1)),sK3(sK2,sK0,k1_tarski(sK1))) ),
    inference(resolution,[],[f202,f127])).

fof(f202,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k6_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,sK4(X1,sK0,k1_tarski(sK1)),sK3(X1,sK0,k1_tarski(sK1))) ) ),
    inference(subsumption_resolution,[],[f201,f38])).

fof(f201,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k6_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,sK4(X1,sK0,k1_tarski(sK1)),sK3(X1,sK0,k1_tarski(sK1)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f200,f91])).

fof(f200,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k6_waybel_0(sK0,sK1))
      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_orders_2(sK0,sK4(X1,sK0,k1_tarski(sK1)),sK3(X1,sK0,k1_tarski(sK1)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f193,f39])).

fof(f193,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k6_waybel_0(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_orders_2(sK0,sK4(X1,sK0,k1_tarski(sK1)),sK3(X1,sK0,k1_tarski(sK1)))
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f42,f110])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_orders_2(X1,sK4(X0,X1,X2),sK3(X0,X1,X2))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f127,plain,(
    r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f125,f110])).

fof(f125,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1))) ),
    inference(subsumption_resolution,[],[f124,f91])).

fof(f124,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1))) ),
    inference(resolution,[],[f103,f62])).

fof(f62,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f103,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,k6_waybel_0(sK0,sK1))
      | r2_hidden(sK2,a_2_1_waybel_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f102,f38])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK1,X0)
      | r2_hidden(sK2,a_2_1_waybel_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f101,f37])).

fof(f101,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK1,X0)
      | r2_hidden(sK2,a_2_1_waybel_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f100,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK1,X0)
      | r2_hidden(sK2,a_2_1_waybel_0(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f99,f39])).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK1,X0)
      | r2_hidden(sK2,a_2_1_waybel_0(sK0,X0)) ) ),
    inference(resolution,[],[f34,f59])).

fof(f59,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r1_orders_2(X1,X4,X3)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X3,a_2_1_waybel_0(X1,X2)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X4,X3)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
