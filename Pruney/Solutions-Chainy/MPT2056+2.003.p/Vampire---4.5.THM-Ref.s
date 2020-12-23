%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:22 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 219 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  231 ( 777 expanded)
%              Number of equality atoms :   47 ( 159 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f495,plain,(
    $false ),
    inference(global_subsumption,[],[f292,f494])).

fof(f494,plain,(
    sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f480,f202])).

fof(f202,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(backward_demodulation,[],[f173,f201])).

fof(f201,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f200,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f200,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f184,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f184,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f74,f45])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f54,f56,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f173,plain,(
    ! [X1] : k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(superposition,[],[f67,f46])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f480,plain,(
    k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f67,f357])).

fof(f357,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f347,f116])).

fof(f116,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f109,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f64,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f109,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f62,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f347,plain,(
    v1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f333,f74])).

fof(f333,plain,(
    v1_xboole_0(k4_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_xboole_0),sK1))) ),
    inference(unit_resulting_resolution,[],[f263,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f76,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f263,plain,(
    r1_xboole_0(k1_tarski(k1_xboole_0),sK1) ),
    inference(unit_resulting_resolution,[],[f254,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f254,plain,(
    ~ r2_hidden(k1_xboole_0,sK1) ),
    inference(unit_resulting_resolution,[],[f43,f35,f93,f69,f70,f71,f68,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | v1_xboole_0(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(definition_unfolding,[],[f48,f47,f47,f47,f47])).

fof(f47,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(X0))
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r2_hidden(X2,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ v1_xboole_0(X2)
              | ~ r2_hidden(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          | ~ v13_waybel_0(X1,k3_yellow_1(X0))
          | ~ v2_waybel_0(X1,k3_yellow_1(X0))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f71,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f36,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f37,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f38,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f93,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f89,f86])).

fof(f86,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f42,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f292,plain,(
    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(superposition,[],[f40,f278])).

fof(f278,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f269,f218])).

fof(f218,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f68,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f269,plain,(
    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f41,f42,f35,f69,f70,f68,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f51,f47,f47,f47,f47])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

fof(f40,plain,(
    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:53:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.13/0.52  % (21454)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.13/0.52  % (21455)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.13/0.52  % (21460)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.13/0.52  % (21450)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.13/0.53  % (21456)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.53  % (21462)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.53  % (21458)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.53  % (21467)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.53  % (21473)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.53  % (21474)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.54  % (21475)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.27/0.54  % (21451)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.54  % (21466)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.54  % (21452)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.54  % (21465)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.54  % (21479)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.27/0.54  % (21459)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.54  % (21478)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.54  % (21453)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.54  % (21470)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.54  % (21457)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.55  % (21464)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.55  % (21461)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.27/0.55  % (21460)Refutation not found, incomplete strategy% (21460)------------------------------
% 1.27/0.55  % (21460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.55  % (21460)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.55  
% 1.27/0.55  % (21460)Memory used [KB]: 10746
% 1.27/0.55  % (21460)Time elapsed: 0.108 s
% 1.27/0.55  % (21460)------------------------------
% 1.27/0.55  % (21460)------------------------------
% 1.27/0.55  % (21471)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.55  % (21477)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.27/0.55  % (21463)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.55  % (21472)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.55  % (21469)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.27/0.55  % (21476)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.56  % (21472)Refutation not found, incomplete strategy% (21472)------------------------------
% 1.27/0.56  % (21472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.56  % (21472)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.56  
% 1.27/0.56  % (21472)Memory used [KB]: 10746
% 1.27/0.56  % (21472)Time elapsed: 0.139 s
% 1.27/0.56  % (21472)------------------------------
% 1.27/0.56  % (21472)------------------------------
% 1.27/0.56  % (21467)Refutation not found, incomplete strategy% (21467)------------------------------
% 1.27/0.56  % (21467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.56  % (21467)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.56  
% 1.27/0.56  % (21467)Memory used [KB]: 10618
% 1.27/0.56  % (21467)Time elapsed: 0.139 s
% 1.27/0.56  % (21467)------------------------------
% 1.27/0.56  % (21467)------------------------------
% 1.27/0.56  % (21452)Refutation not found, incomplete strategy% (21452)------------------------------
% 1.27/0.56  % (21452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.56  % (21452)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.56  
% 1.27/0.56  % (21452)Memory used [KB]: 10746
% 1.27/0.56  % (21452)Time elapsed: 0.121 s
% 1.27/0.56  % (21452)------------------------------
% 1.27/0.56  % (21452)------------------------------
% 1.27/0.56  % (21474)Refutation found. Thanks to Tanya!
% 1.27/0.56  % SZS status Theorem for theBenchmark
% 1.27/0.56  % SZS output start Proof for theBenchmark
% 1.27/0.56  fof(f495,plain,(
% 1.27/0.56    $false),
% 1.27/0.56    inference(global_subsumption,[],[f292,f494])).
% 1.27/0.56  fof(f494,plain,(
% 1.27/0.56    sK1 = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.27/0.56    inference(forward_demodulation,[],[f480,f202])).
% 1.27/0.56  fof(f202,plain,(
% 1.27/0.56    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 1.27/0.56    inference(backward_demodulation,[],[f173,f201])).
% 1.27/0.56  fof(f201,plain,(
% 1.27/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.27/0.56    inference(forward_demodulation,[],[f200,f45])).
% 1.27/0.56  fof(f45,plain,(
% 1.27/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f11])).
% 1.27/0.56  fof(f11,axiom,(
% 1.27/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.27/0.56  fof(f200,plain,(
% 1.27/0.56    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.27/0.56    inference(forward_demodulation,[],[f184,f46])).
% 1.27/0.56  fof(f46,plain,(
% 1.27/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.27/0.56    inference(cnf_transformation,[],[f9])).
% 1.27/0.56  fof(f9,axiom,(
% 1.27/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.27/0.56  fof(f184,plain,(
% 1.27/0.56    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.27/0.56    inference(superposition,[],[f74,f45])).
% 1.27/0.56  fof(f74,plain,(
% 1.27/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.27/0.56    inference(definition_unfolding,[],[f54,f56,f56])).
% 1.27/0.56  fof(f56,plain,(
% 1.27/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.27/0.56    inference(cnf_transformation,[],[f10])).
% 1.27/0.56  fof(f10,axiom,(
% 1.27/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.27/0.56  fof(f54,plain,(
% 1.27/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f1])).
% 1.27/0.56  fof(f1,axiom,(
% 1.27/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.27/0.56  fof(f173,plain,(
% 1.27/0.56    ( ! [X1] : (k5_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 1.27/0.56    inference(superposition,[],[f67,f46])).
% 1.27/0.56  fof(f67,plain,(
% 1.27/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.27/0.56    inference(definition_unfolding,[],[f55,f56])).
% 1.27/0.56  fof(f55,plain,(
% 1.27/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.27/0.56    inference(cnf_transformation,[],[f7])).
% 1.27/0.56  fof(f7,axiom,(
% 1.27/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.27/0.56  fof(f480,plain,(
% 1.27/0.56    k4_xboole_0(sK1,k1_tarski(k1_xboole_0)) = k5_xboole_0(sK1,k1_xboole_0)),
% 1.27/0.56    inference(superposition,[],[f67,f357])).
% 1.27/0.56  fof(f357,plain,(
% 1.27/0.56    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(k1_xboole_0)))),
% 1.27/0.56    inference(unit_resulting_resolution,[],[f347,f116])).
% 1.27/0.56  fof(f116,plain,(
% 1.27/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.27/0.56    inference(resolution,[],[f109,f99])).
% 1.27/0.56  fof(f99,plain,(
% 1.27/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.27/0.56    inference(resolution,[],[f64,f53])).
% 1.27/0.56  fof(f53,plain,(
% 1.27/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f2])).
% 1.27/0.56  fof(f2,axiom,(
% 1.27/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.27/0.56  fof(f64,plain,(
% 1.27/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f33])).
% 1.27/0.56  fof(f33,plain,(
% 1.27/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.27/0.56    inference(ennf_transformation,[],[f3])).
% 1.27/0.56  fof(f3,axiom,(
% 1.27/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.27/0.56  fof(f109,plain,(
% 1.27/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.27/0.56    inference(resolution,[],[f62,f44])).
% 1.27/0.56  fof(f44,plain,(
% 1.27/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f8])).
% 1.27/0.56  fof(f8,axiom,(
% 1.27/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.27/0.56  fof(f62,plain,(
% 1.27/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.27/0.56    inference(cnf_transformation,[],[f6])).
% 1.27/0.56  fof(f6,axiom,(
% 1.27/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.27/0.56  fof(f347,plain,(
% 1.27/0.56    v1_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k1_tarski(k1_xboole_0))))),
% 1.27/0.56    inference(forward_demodulation,[],[f333,f74])).
% 1.27/0.56  fof(f333,plain,(
% 1.27/0.56    v1_xboole_0(k4_xboole_0(k1_tarski(k1_xboole_0),k4_xboole_0(k1_tarski(k1_xboole_0),sK1)))),
% 1.27/0.56    inference(unit_resulting_resolution,[],[f263,f151])).
% 1.27/0.56  fof(f151,plain,(
% 1.27/0.56    ( ! [X0,X1] : (v1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.27/0.56    inference(resolution,[],[f76,f52])).
% 1.27/0.56  fof(f52,plain,(
% 1.27/0.56    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f2])).
% 1.27/0.56  fof(f76,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.27/0.56    inference(definition_unfolding,[],[f57,f56])).
% 1.27/0.56  fof(f57,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f31])).
% 1.27/0.56  fof(f31,plain,(
% 1.27/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.27/0.56    inference(ennf_transformation,[],[f21])).
% 1.27/0.56  fof(f21,plain,(
% 1.27/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.27/0.56    inference(rectify,[],[f5])).
% 1.27/0.56  fof(f5,axiom,(
% 1.27/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.27/0.56  fof(f263,plain,(
% 1.27/0.56    r1_xboole_0(k1_tarski(k1_xboole_0),sK1)),
% 1.27/0.56    inference(unit_resulting_resolution,[],[f254,f59])).
% 1.27/0.56  fof(f59,plain,(
% 1.27/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f32])).
% 1.27/0.56  fof(f32,plain,(
% 1.27/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.27/0.56    inference(ennf_transformation,[],[f12])).
% 1.27/0.56  fof(f12,axiom,(
% 1.27/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.27/0.56  fof(f254,plain,(
% 1.27/0.56    ~r2_hidden(k1_xboole_0,sK1)),
% 1.27/0.56    inference(unit_resulting_resolution,[],[f43,f35,f93,f69,f70,f71,f68,f72])).
% 1.27/0.56  fof(f72,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | v1_xboole_0(X0) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) )),
% 1.27/0.56    inference(definition_unfolding,[],[f48,f47,f47,f47,f47])).
% 1.27/0.56  fof(f47,plain,(
% 1.27/0.56    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.27/0.56    inference(cnf_transformation,[],[f16])).
% 1.27/0.56  fof(f16,axiom,(
% 1.27/0.56    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).
% 1.27/0.56  fof(f48,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r2_hidden(X2,X1) | ~v1_xboole_0(X2)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f25])).
% 1.27/0.56  fof(f25,plain,(
% 1.27/0.56    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.27/0.56    inference(flattening,[],[f24])).
% 1.27/0.56  fof(f24,plain,(
% 1.27/0.56    ! [X0] : (! [X1] : (! [X2] : (~v1_xboole_0(X2) | ~r2_hidden(X2,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~v2_waybel_0(X1,k3_yellow_1(X0)) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.27/0.56    inference(ennf_transformation,[],[f18])).
% 1.27/0.56  fof(f18,axiom,(
% 1.27/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 1.27/0.56  fof(f68,plain,(
% 1.27/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.27/0.56    inference(definition_unfolding,[],[f39,f47])).
% 1.27/0.56  fof(f39,plain,(
% 1.27/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f23,plain,(
% 1.27/0.56    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.27/0.56    inference(flattening,[],[f22])).
% 1.27/0.56  fof(f22,plain,(
% 1.27/0.56    ? [X0] : (? [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) != X1 & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.27/0.56    inference(ennf_transformation,[],[f20])).
% 1.27/0.56  fof(f20,negated_conjecture,(
% 1.27/0.56    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.27/0.56    inference(negated_conjecture,[],[f19])).
% 1.27/0.56  fof(f19,conjecture,(
% 1.27/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 1.27/0.56  fof(f71,plain,(
% 1.27/0.56    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.27/0.56    inference(definition_unfolding,[],[f36,f47])).
% 1.27/0.56  fof(f36,plain,(
% 1.27/0.56    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f70,plain,(
% 1.27/0.56    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.27/0.56    inference(definition_unfolding,[],[f37,f47])).
% 1.27/0.56  fof(f37,plain,(
% 1.27/0.56    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f69,plain,(
% 1.27/0.56    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.27/0.56    inference(definition_unfolding,[],[f38,f47])).
% 1.27/0.56  fof(f38,plain,(
% 1.27/0.56    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f93,plain,(
% 1.27/0.56    ~v1_xboole_0(k2_struct_0(sK0))),
% 1.27/0.56    inference(forward_demodulation,[],[f89,f86])).
% 1.27/0.56  fof(f86,plain,(
% 1.27/0.56    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.27/0.56    inference(unit_resulting_resolution,[],[f42,f49])).
% 1.27/0.56  fof(f49,plain,(
% 1.27/0.56    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f26])).
% 1.27/0.56  fof(f26,plain,(
% 1.27/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.27/0.56    inference(ennf_transformation,[],[f14])).
% 1.27/0.56  fof(f14,axiom,(
% 1.27/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.27/0.56  fof(f42,plain,(
% 1.27/0.56    l1_struct_0(sK0)),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f89,plain,(
% 1.27/0.56    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.27/0.56    inference(unit_resulting_resolution,[],[f41,f42,f50])).
% 1.27/0.56  fof(f50,plain,(
% 1.27/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.27/0.56    inference(cnf_transformation,[],[f28])).
% 1.27/0.56  fof(f28,plain,(
% 1.27/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.27/0.56    inference(flattening,[],[f27])).
% 1.27/0.56  fof(f27,plain,(
% 1.27/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.27/0.56    inference(ennf_transformation,[],[f15])).
% 1.27/0.56  fof(f15,axiom,(
% 1.27/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.27/0.56  fof(f41,plain,(
% 1.27/0.56    ~v2_struct_0(sK0)),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f35,plain,(
% 1.27/0.56    ~v1_xboole_0(sK1)),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  fof(f43,plain,(
% 1.27/0.56    v1_xboole_0(k1_xboole_0)),
% 1.27/0.56    inference(cnf_transformation,[],[f4])).
% 1.27/0.56  fof(f4,axiom,(
% 1.27/0.56    v1_xboole_0(k1_xboole_0)),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.27/0.56  fof(f292,plain,(
% 1.27/0.56    sK1 != k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.27/0.56    inference(superposition,[],[f40,f278])).
% 1.27/0.56  fof(f278,plain,(
% 1.27/0.56    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k1_tarski(k1_xboole_0))),
% 1.27/0.56    inference(forward_demodulation,[],[f269,f218])).
% 1.27/0.56  fof(f218,plain,(
% 1.27/0.56    ( ! [X0] : (k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 1.27/0.56    inference(unit_resulting_resolution,[],[f68,f66])).
% 1.27/0.56  fof(f66,plain,(
% 1.27/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.27/0.56    inference(cnf_transformation,[],[f34])).
% 1.27/0.56  fof(f34,plain,(
% 1.27/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.27/0.56    inference(ennf_transformation,[],[f13])).
% 1.27/0.56  fof(f13,axiom,(
% 1.27/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.27/0.56  fof(f269,plain,(
% 1.27/0.56    k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))),sK1,k1_tarski(k1_xboole_0))),
% 1.27/0.56    inference(unit_resulting_resolution,[],[f41,f42,f35,f69,f70,f68,f73])).
% 1.27/0.56  fof(f73,plain,(
% 1.27/0.56    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = k7_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))),X1,k1_tarski(k1_xboole_0)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | v2_struct_0(X0)) )),
% 1.27/0.56    inference(definition_unfolding,[],[f51,f47,f47,f47,f47])).
% 1.27/0.56  fof(f51,plain,(
% 1.27/0.56    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )),
% 1.27/0.56    inference(cnf_transformation,[],[f30])).
% 1.27/0.56  fof(f30,plain,(
% 1.27/0.56    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.27/0.56    inference(flattening,[],[f29])).
% 1.27/0.56  fof(f29,plain,(
% 1.27/0.56    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.27/0.56    inference(ennf_transformation,[],[f17])).
% 1.27/0.56  fof(f17,axiom,(
% 1.27/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & ~v1_xboole_0(X1)) => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))),X1,k1_tarski(k1_xboole_0)) = k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))),
% 1.27/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).
% 1.27/0.56  fof(f40,plain,(
% 1.27/0.56    sK1 != k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 1.27/0.56    inference(cnf_transformation,[],[f23])).
% 1.27/0.56  % SZS output end Proof for theBenchmark
% 1.27/0.56  % (21474)------------------------------
% 1.27/0.56  % (21474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.56  % (21474)Termination reason: Refutation
% 1.27/0.56  
% 1.27/0.56  % (21474)Memory used [KB]: 6524
% 1.27/0.56  % (21474)Time elapsed: 0.151 s
% 1.27/0.56  % (21474)------------------------------
% 1.27/0.56  % (21474)------------------------------
% 1.27/0.56  % (21476)Refutation not found, incomplete strategy% (21476)------------------------------
% 1.27/0.56  % (21476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.56  % (21449)Success in time 0.197 s
%------------------------------------------------------------------------------
