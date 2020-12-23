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
% DateTime   : Thu Dec  3 13:16:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 164 expanded)
%              Number of leaves         :   15 (  40 expanded)
%              Depth                    :   22
%              Number of atoms          :  407 ( 570 expanded)
%              Number of equality atoms :   22 (  63 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(global_subsumption,[],[f36,f38,f153])).

fof(f153,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f150,f37])).

fof(f37,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f147,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f139,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_yellow_0(k2_yellow_1(X0))
      | ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | ~ v1_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f116,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f116,plain,(
    ! [X0] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(k1_xboole_0,X0)
      | ~ v1_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f104,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_yellow_0(k2_yellow_1(X0)),X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_yellow_0(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(global_subsumption,[],[f41,f42,f68,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0)
      | v1_xboole_0(X0)
      | r1_tarski(k3_yellow_0(k2_yellow_1(X0)),X1)
      | ~ v5_orders_2(k2_yellow_1(X0))
      | ~ v1_yellow_0(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | r1_tarski(k3_yellow_0(k2_yellow_1(X0)),X1)
      | ~ v5_orders_2(k2_yellow_1(X0))
      | ~ v1_yellow_0(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f99,f43])).

fof(f43,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | r1_tarski(k3_yellow_0(k2_yellow_1(X0)),X1)
      | ~ v5_orders_2(k2_yellow_1(X0))
      | ~ v1_yellow_0(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f96,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0)
      | r1_tarski(X1,X2) ) ),
    inference(global_subsumption,[],[f40,f42,f45,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0)
      | r1_tarski(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(forward_demodulation,[],[f93,f43])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(forward_demodulation,[],[f91,f43])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f60,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(forward_demodulation,[],[f85,f43])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f47,f43])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f40,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) ),
    inference(superposition,[],[f65,f63])).

fof(f63,plain,(
    ! [X0] : k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) ),
    inference(resolution,[],[f48,f42])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f65,plain,(
    ! [X0,X1] : m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),X0) ),
    inference(global_subsumption,[],[f42,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f58,f43])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f42,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f41,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f139,plain,(
    ! [X0] :
      ( v1_yellow_0(k2_yellow_1(X0))
      | ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(k1_xboole_0,X0)
      | ~ m1_subset_1(k1_xboole_0,X0)
      | v1_yellow_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f135,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_yellow_0(k2_yellow_1(X0)) ) ),
    inference(global_subsumption,[],[f42,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),X0,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | v1_yellow_0(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f51,f43])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v1_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f134,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1))
      | r1_lattice3(k2_yellow_1(X0),X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f40,f42,f45,f78,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X2,X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1)) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X2,X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) ) ),
    inference(forward_demodulation,[],[f131,f43])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X2,X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) ) ),
    inference(forward_demodulation,[],[f127,f43])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) ) ),
    inference(resolution,[],[f98,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(forward_demodulation,[],[f83,f43])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f46,f43])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,sK2(X0,X2,X1))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | r1_lattice3(X0,X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r3_orders_2(X0,X1,sK2(X0,X2,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X2,X1) ) ),
    inference(resolution,[],[f61,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X1,X2) ) ),
    inference(superposition,[],[f53,f43])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (7450)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (7457)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (7448)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (7463)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  % (7458)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.50  % (7464)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.50  % (7446)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (7462)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.51  % (7457)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(global_subsumption,[],[f36,f38,f153])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) | v1_xboole_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f150,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    r2_hidden(k1_xboole_0,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.51    inference(negated_conjecture,[],[f15])).
% 0.20/0.51  fof(f15,conjecture,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(resolution,[],[f147,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f146])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(resolution,[],[f139,f126])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_yellow_0(k2_yellow_1(X0)) | ~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f125])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(k1_xboole_0,X0) | ~v1_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(resolution,[],[f116,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ( ! [X0] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(k1_xboole_0,X0) | ~v1_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(resolution,[],[f104,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k3_yellow_0(k2_yellow_1(X0)),X1) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | ~v1_yellow_0(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(global_subsumption,[],[f41,f42,f68,f103])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) | v1_xboole_0(X0) | r1_tarski(k3_yellow_0(k2_yellow_1(X0)),X1) | ~v5_orders_2(k2_yellow_1(X0)) | ~v1_yellow_0(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | r1_tarski(k3_yellow_0(k2_yellow_1(X0)),X1) | ~v5_orders_2(k2_yellow_1(X0)) | ~v1_yellow_0(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f99,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | r1_tarski(k3_yellow_0(k2_yellow_1(X0)),X1) | ~v5_orders_2(k2_yellow_1(X0)) | ~v1_yellow_0(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(resolution,[],[f96,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0) | r1_tarski(X1,X2)) )),
% 0.20/0.51    inference(global_subsumption,[],[f40,f42,f45,f95])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~v3_orders_2(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0)) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0) | r1_tarski(X1,X2)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~v3_orders_2(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0)) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f93,f43])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~v3_orders_2(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~v3_orders_2(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f91,f43])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v3_orders_2(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,X0)) )),
% 0.20/0.51    inference(resolution,[],[f60,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f85,f43])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f47,f43])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0)) )),
% 0.20/0.51    inference(superposition,[],[f65,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0] : (k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)) )),
% 0.20/0.51    inference(resolution,[],[f48,f42])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),X0)) )),
% 0.20/0.51    inference(global_subsumption,[],[f42,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(k2_yellow_1(X0),X1),X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(superposition,[],[f58,f43])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    ( ! [X0] : (v1_yellow_0(k2_yellow_1(X0)) | ~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f137])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,X0) | v1_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(resolution,[],[f135,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),X0,X1) | ~m1_subset_1(X1,X0) | v1_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(global_subsumption,[],[f42,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),X0,X1) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | v1_yellow_0(k2_yellow_1(X0))) )),
% 0.20/0.51    inference(superposition,[],[f51,f43])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v1_yellow_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : ((v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => (v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) | v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f134,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1)) | r1_lattice3(k2_yellow_1(X0),X2,X1) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.51    inference(global_subsumption,[],[f40,f42,f45,f78,f133])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X2,X1) | v1_xboole_0(X0) | ~r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1))) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f132])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X2,X1) | v1_xboole_0(X0) | ~r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f131,f43])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X2,X1) | v1_xboole_0(X0) | ~r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f130])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f127,f43])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),u1_struct_0(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~r1_tarski(X1,sK2(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(sK2(k2_yellow_1(X0),X2,X1),X0)) )),
% 0.20/0.51    inference(resolution,[],[f98,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f83,f43])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f46,f43])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,sK2(X0,X2,X1)) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0)) | v2_struct_0(X0) | ~v3_orders_2(X0) | r1_lattice3(X0,X2,X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(sK2(X0,X2,X1),u1_struct_0(X0)) | v2_struct_0(X0) | ~r3_orders_2(X0,X1,sK2(X0,X2,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X2,X1)) )),
% 0.20/0.51    inference(resolution,[],[f61,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r3_orders_2(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X1,X2)) )),
% 0.20/0.51    inference(superposition,[],[f53,f43])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ~v1_xboole_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (7457)------------------------------
% 0.20/0.51  % (7457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7457)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (7457)Memory used [KB]: 10746
% 0.20/0.51  % (7457)Time elapsed: 0.077 s
% 0.20/0.51  % (7457)------------------------------
% 0.20/0.51  % (7457)------------------------------
% 0.20/0.51  % (7448)Refutation not found, incomplete strategy% (7448)------------------------------
% 0.20/0.51  % (7448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7448)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7448)Memory used [KB]: 10618
% 0.20/0.51  % (7448)Time elapsed: 0.083 s
% 0.20/0.51  % (7448)------------------------------
% 0.20/0.51  % (7448)------------------------------
% 0.20/0.51  % (7444)Success in time 0.153 s
%------------------------------------------------------------------------------
