%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 (1933 expanded)
%              Number of leaves         :   12 ( 432 expanded)
%              Depth                    :   49
%              Number of atoms          :  782 (10620 expanded)
%              Number of equality atoms :   23 ( 420 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(subsumption_resolution,[],[f166,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f53,f83])).

fof(f83,plain,(
    ! [X0] : sK3(X0) = X0 ),
    inference(subsumption_resolution,[],[f82,f54])).

fof(f54,plain,(
    ! [X0] : ~ v1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f82,plain,(
    ! [X0] :
      ( sK3(X0) = X0
      | v1_subset_1(sK3(X0),X0) ) ),
    inference(resolution,[],[f55,f53])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f166,plain,(
    ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f165,f76])).

fof(f76,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f48,f75])).

fof(f75,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
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
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f165,plain,(
    ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f164,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f164,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f163,f63])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f46,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f19])).

fof(f163,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f162,f64])).

fof(f64,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f41,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f162,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f161,f65])).

fof(f65,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f40,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f161,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f160,f38])).

fof(f38,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f160,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f159,f80])).

fof(f80,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f79,f43])).

fof(f79,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f78,f75])).

fof(f78,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f51,f76])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f159,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f75])).

fof(f158,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f157,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f46,f46,f46])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f157,plain,(
    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f156,f154])).

fof(f154,plain,(
    ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(resolution,[],[f153,f36])).

fof(f36,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f153,plain,(
    r1_waybel_7(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f152,f84])).

fof(f152,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f151,f76])).

fof(f151,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f150,f43])).

fof(f150,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f63])).

fof(f149,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f148,f64])).

fof(f148,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f147,f65])).

fof(f147,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f146,f38])).

fof(f146,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f145,f80])).

fof(f145,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f144,f75])).

fof(f144,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f143,f69])).

fof(f143,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f142,f77])).

fof(f77,plain,(
    m1_subset_1(sK2,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f37,f76])).

fof(f37,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f142,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK2,k2_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(resolution,[],[f140,f35])).

fof(f35,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f140,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | r1_waybel_7(sK0,sK1,X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f139,f76])).

fof(f139,plain,(
    ! [X0] :
      ( r1_waybel_7(sK0,sK1,X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(subsumption_resolution,[],[f138,f44])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f138,plain,(
    ! [X0] :
      ( r1_waybel_7(sK0,sK1,X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(subsumption_resolution,[],[f137,f105])).

fof(f105,plain,(
    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f104,f63])).

fof(f104,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f103,f38])).

fof(f103,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f102,f65])).

fof(f102,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f101,f64])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f100,f80])).

fof(f100,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(sK0))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f99,f84])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0) ) ),
    inference(forward_demodulation,[],[f98,f76])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0) ) ),
    inference(subsumption_resolution,[],[f97,f43])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0) ) ),
    inference(resolution,[],[f70,f75])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f60,f46,f46,f46])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f137,plain,(
    ! [X0] :
      ( r1_waybel_7(sK0,sK1,X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(subsumption_resolution,[],[f136,f43])).

fof(f136,plain,(
    ! [X0] :
      ( r1_waybel_7(sK0,sK1,X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(subsumption_resolution,[],[f135,f45])).

fof(f135,plain,(
    ! [X0] :
      ( r1_waybel_7(sK0,sK1,X0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(superposition,[],[f118,f133])).

fof(f133,plain,(
    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f132,f63])).

fof(f132,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f131,f38])).

fof(f131,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f130,f65])).

fof(f130,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f129,f66])).

fof(f66,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f39,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f129,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f128,f64])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f127,f43])).

fof(f127,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 ) ),
    inference(resolution,[],[f67,f75])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ),
    inference(definition_unfolding,[],[f52,f46,f46,f46,f46])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f118,plain,(
    ! [X0,X1] :
      ( r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) ) ),
    inference(subsumption_resolution,[],[f116,f96])).

fof(f96,plain,(
    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f95,f63])).

fof(f95,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f94,f38])).

fof(f94,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f93,f65])).

fof(f93,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f92,f64])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),X0)) ) ),
    inference(subsumption_resolution,[],[f91,f80])).

fof(f91,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(sK0))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),X0)) ) ),
    inference(resolution,[],[f90,f84])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | v4_orders_2(k3_yellow19(sK0,X0,X1)) ) ),
    inference(forward_demodulation,[],[f89,f76])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | v4_orders_2(k3_yellow19(sK0,X0,X1)) ) ),
    inference(subsumption_resolution,[],[f88,f43])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | v4_orders_2(k3_yellow19(sK0,X0,X1)) ) ),
    inference(resolution,[],[f68,f75])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | v4_orders_2(k3_yellow19(X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f58,f46,f46,f46])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v4_orders_2(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
      | ~ r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) ) ),
    inference(resolution,[],[f115,f50])).

% (29007)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).

fof(f115,plain,(
    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f114,f63])).

fof(f114,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f113,f38])).

fof(f113,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f112,f65])).

fof(f112,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f111,f66])).

fof(f111,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f110,f64])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),X0)) ) ),
    inference(subsumption_resolution,[],[f109,f80])).

fof(f109,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(sK0))
      | v1_xboole_0(X0)
      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),X0)) ) ),
    inference(resolution,[],[f108,f84])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | v7_waybel_0(k3_yellow19(sK0,X0,X1)) ) ),
    inference(forward_demodulation,[],[f107,f76])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | v7_waybel_0(k3_yellow19(sK0,X0,X1)) ) ),
    inference(subsumption_resolution,[],[f106,f43])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | v7_waybel_0(k3_yellow19(sK0,X0,X1)) ) ),
    inference(resolution,[],[f72,f75])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | v7_waybel_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f62,f46,f46,f46,f46])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v7_waybel_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f156,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(subsumption_resolution,[],[f155,f77])).

fof(f155,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK2,k2_struct_0(sK0))
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(resolution,[],[f153,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,sK1,X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(backward_demodulation,[],[f124,f133])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(forward_demodulation,[],[f123,f76])).

fof(f123,plain,(
    ! [X0] :
      ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(subsumption_resolution,[],[f122,f105])).

fof(f122,plain,(
    ! [X0] :
      ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(subsumption_resolution,[],[f121,f43])).

fof(f121,plain,(
    ! [X0] :
      ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(subsumption_resolution,[],[f120,f45])).

fof(f120,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) ) ),
    inference(resolution,[],[f119,f44])).

fof(f119,plain,(
    ! [X2,X3] :
      ( ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(X2)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3)
      | r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) ) ),
    inference(subsumption_resolution,[],[f117,f96])).

fof(f117,plain,(
    ! [X2,X3] :
      ( ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
      | v2_struct_0(X2)
      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3)
      | r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3) ) ),
    inference(resolution,[],[f115,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:48:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (28993)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (28991)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (28993)Refutation not found, incomplete strategy% (28993)------------------------------
% 0.21/0.54  % (28993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28991)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (29009)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (28993)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28993)Memory used [KB]: 10746
% 0.21/0.55  % (28993)Time elapsed: 0.124 s
% 0.21/0.55  % (28993)------------------------------
% 0.21/0.55  % (28993)------------------------------
% 0.21/0.55  % (28985)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (28999)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f166,f84])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(backward_demodulation,[],[f53,f83])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X0] : (sK3(X0) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f82,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_subset_1(sK3(X0),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X0] : (sK3(X0) = X0 | v1_subset_1(sK3(X0),X0)) )),
% 0.21/0.55    inference(resolution,[],[f55,f53])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.55    inference(forward_demodulation,[],[f165,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.55    inference(resolution,[],[f48,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    l1_struct_0(sK0)),
% 0.21/0.55    inference(resolution,[],[f47,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    l1_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.21/0.55    inference(negated_conjecture,[],[f12])).
% 0.21/0.55  fof(f12,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f164,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ~v2_struct_0(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f163,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 0.21/0.55    inference(definition_unfolding,[],[f42,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f162,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.55    inference(definition_unfolding,[],[f41,f46])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f161,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 0.21/0.55    inference(definition_unfolding,[],[f40,f46])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f160,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ~v1_xboole_0(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f160,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f159,f80])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.55    inference(subsumption_resolution,[],[f79,f43])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ~v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f78,f75])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.55    inference(superposition,[],[f51,f76])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f158,f75])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(resolution,[],[f157,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f57,f46,f46,f46])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v2_struct_0(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.55    inference(subsumption_resolution,[],[f156,f154])).
% 0.21/0.55  fof(f154,plain,(
% 0.21/0.55    ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.55    inference(resolution,[],[f153,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f152,f84])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.55    inference(forward_demodulation,[],[f151,f76])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f150,f43])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f149,f63])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f148,f64])).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f147,f65])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f146,f38])).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    r1_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f145,f80])).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    r1_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f144,f75])).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    r1_waybel_7(sK0,sK1,sK2) | ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v2_struct_0(sK0)),
% 0.21/0.55    inference(resolution,[],[f143,f69])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f142,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.21/0.55    inference(backward_demodulation,[],[f37,f76])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    r1_waybel_7(sK0,sK1,sK2) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK2,k2_struct_0(sK0))),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f141])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    r1_waybel_7(sK0,sK1,sK2) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK2,k2_struct_0(sK0)) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.55    inference(resolution,[],[f140,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f140,plain,(
% 0.21/0.55    ( ! [X0] : (~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r1_waybel_7(sK0,sK1,X0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(X0,k2_struct_0(sK0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f139,f76])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    ( ! [X0] : (r1_waybel_7(sK0,sK1,X0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f138,f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    v2_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    ( ! [X0] : (r1_waybel_7(sK0,sK1,X0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f137,f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f104,f63])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f103,f38])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.55    inference(subsumption_resolution,[],[f102,f65])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.55    inference(resolution,[],[f101,f64])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X0] : (~v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),X0),sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f100,f80])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ( ! [X0] : (v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(X0) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),X0),sK0)) )),
% 0.21/0.55    inference(resolution,[],[f99,f84])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f98,f76])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f97,f43])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | l1_waybel_0(k3_yellow19(sK0,X0,X1),sK0)) )),
% 0.21/0.55    inference(resolution,[],[f70,f75])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f60,f46,f46,f46])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    ( ! [X0] : (r1_waybel_7(sK0,sK1,X0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f136,f43])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    ( ! [X0] : (r1_waybel_7(sK0,sK1,X0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f135,f45])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    ( ! [X0] : (r1_waybel_7(sK0,sK1,X0) | ~l1_pre_topc(sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) )),
% 0.21/0.55    inference(superposition,[],[f118,f133])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.55    inference(subsumption_resolution,[],[f132,f63])).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.55    inference(subsumption_resolution,[],[f131,f38])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.55    inference(subsumption_resolution,[],[f130,f65])).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.55    inference(subsumption_resolution,[],[f129,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 0.21/0.55    inference(definition_unfolding,[],[f39,f46])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.55    inference(resolution,[],[f128,f64])).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    ( ! [X0] : (~v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f127,f43])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    ( ! [X0] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0) )),
% 0.21/0.55    inference(resolution,[],[f67,f75])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1) )),
% 0.21/0.55    inference(definition_unfolding,[],[f52,f46,f46,f46,f46])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~l1_pre_topc(X0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(X0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f116,f96])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.55    inference(subsumption_resolution,[],[f95,f63])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.55    inference(subsumption_resolution,[],[f94,f38])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.55    inference(subsumption_resolution,[],[f93,f65])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.55    inference(resolution,[],[f92,f64])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    ( ! [X0] : (~v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),X0))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f91,f80])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ( ! [X0] : (v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(X0) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),X0))) )),
% 0.21/0.55    inference(resolution,[],[f90,f84])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v4_orders_2(k3_yellow19(sK0,X0,X1))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f89,f76])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v4_orders_2(k3_yellow19(sK0,X0,X1))) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f88,f43])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v4_orders_2(k3_yellow19(sK0,X0,X1))) )),
% 0.21/0.55    inference(resolution,[],[f68,f75])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | v4_orders_2(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f58,f46,f46,f46])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v4_orders_2(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(X0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_waybel_7(X0,k2_yellow19(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | ~r3_waybel_9(X0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)) )),
% 0.21/0.55    inference(resolution,[],[f115,f50])).
% 0.21/0.56  % (29007)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.56    inference(subsumption_resolution,[],[f114,f63])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.56    inference(subsumption_resolution,[],[f113,f38])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.56    inference(subsumption_resolution,[],[f112,f65])).
% 0.21/0.56  fof(f112,plain,(
% 0.21/0.56    ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.56    inference(subsumption_resolution,[],[f111,f66])).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    ~v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.56    inference(resolution,[],[f110,f64])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    ( ! [X0] : (~v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),X0))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f109,f80])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ( ! [X0] : (v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(X0) | ~v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) | ~v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),X0))) )),
% 0.21/0.56    inference(resolution,[],[f108,f84])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v7_waybel_0(k3_yellow19(sK0,X0,X1))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f107,f76])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v7_waybel_0(k3_yellow19(sK0,X0,X1))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f106,f43])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v7_waybel_0(k3_yellow19(sK0,X0,X1))) )),
% 0.21/0.56    inference(resolution,[],[f72,f75])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | v7_waybel_0(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f62,f46,f46,f46,f46])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v7_waybel_0(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.56    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f155,f77])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(sK2,k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.56    inference(resolution,[],[f153,f134])).
% 0.21/0.56  fof(f134,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f124,f133])).
% 0.21/0.56  fof(f124,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(X0,k2_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f123,f76])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    ( ! [X0] : (v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f122,f105])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    ( ! [X0] : (v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f121,f43])).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    ( ! [X0] : (v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f120,f45])).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(sK0) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) )),
% 0.21/0.56    inference(resolution,[],[f119,f44])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(X2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3) | r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f117,f96])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(X2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_waybel_7(X2,k2_yellow19(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X3) | r3_waybel_9(X2,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X3)) )),
% 0.21/0.56    inference(resolution,[],[f115,f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | r3_waybel_9(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (28991)------------------------------
% 0.21/0.56  % (28991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28991)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (28991)Memory used [KB]: 6268
% 0.21/0.56  % (28991)Time elapsed: 0.128 s
% 0.21/0.56  % (28991)------------------------------
% 0.21/0.56  % (28991)------------------------------
% 1.53/0.56  % (28984)Success in time 0.197 s
%------------------------------------------------------------------------------
