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
% DateTime   : Thu Dec  3 13:16:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 381 expanded)
%              Number of leaves         :   21 ( 129 expanded)
%              Depth                    :   15
%              Number of atoms          :  348 ( 962 expanded)
%              Number of equality atoms :   83 ( 433 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(subsumption_resolution,[],[f181,f164])).

fof(f164,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) != k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f163])).

fof(f163,plain,
    ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) != k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2))
    | k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) != k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(backward_demodulation,[],[f75,f160])).

fof(f160,plain,(
    k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) = k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(backward_demodulation,[],[f145,f155])).

fof(f155,plain,(
    k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(subsumption_resolution,[],[f154,f89])).

fof(f89,plain,(
    m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(backward_demodulation,[],[f77,f56])).

fof(f56,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f77,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f42,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
      | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
              | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
        & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) )
   => ( ? [X2] :
          ( ( k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2)
            | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ( k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2)
          | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
   => ( ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
        | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
            | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
           => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
              & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
            & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).

fof(f154,plain,
    ( k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(subsumption_resolution,[],[f148,f90])).

fof(f90,plain,(
    m1_subset_1(sK2,k9_setfam_1(sK0)) ),
    inference(backward_demodulation,[],[f76,f56])).

fof(f76,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f148,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(resolution,[],[f138,f115])).

fof(f115,plain,(
    r2_hidden(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),k9_setfam_1(sK0)) ),
    inference(resolution,[],[f112,f90])).

fof(f112,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k9_setfam_1(sK0))
      | r2_hidden(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k9_setfam_1(sK0)) ) ),
    inference(resolution,[],[f111,f89])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f110,f56])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k9_setfam_1(X0))
      | r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) ) ),
    inference(forward_demodulation,[],[f88,f56])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) ) ),
    inference(definition_unfolding,[],[f67,f74,f42,f42])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f64,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f64,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l19_yellow_1)).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X0)
      | ~ m1_subset_1(X2,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(forward_demodulation,[],[f137,f56])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
      | ~ r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(forward_demodulation,[],[f136,f56])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
      | ~ r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(subsumption_resolution,[],[f85,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
      | ~ r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f58,f74,f74])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k3_xboole_0(X1,X2),X0)
               => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).

fof(f145,plain,(
    k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(resolution,[],[f142,f89])).

fof(f142,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(sK0))
      | k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) ) ),
    inference(subsumption_resolution,[],[f140,f97])).

fof(f97,plain,(
    ! [X0] : v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) ),
    inference(subsumption_resolution,[],[f96,f82])).

fof(f82,plain,(
    ! [X0] : ~ v2_struct_0(k2_yellow_1(k9_setfam_1(X0))) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f43,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f96,plain,(
    ! [X0] :
      ( v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v2_struct_0(k2_yellow_1(k9_setfam_1(X0))) ) ),
    inference(subsumption_resolution,[],[f95,f51])).

fof(f51,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f95,plain,(
    ! [X0] :
      ( v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(k9_setfam_1(X0)))
      | v2_struct_0(k2_yellow_1(k9_setfam_1(X0))) ) ),
    inference(resolution,[],[f61,f83])).

fof(f83,plain,(
    ! [X0] : v3_lattice3(k2_yellow_1(k9_setfam_1(X0))) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f49,plain,(
    ! [X0] : v3_lattice3(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_lattice3(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_yellow_1)).

fof(f61,plain,(
    ! [X0] :
      ( ~ v3_lattice3(X0)
      | v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0) )
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0) )
      | ~ v3_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v3_lattice3(X0)
       => ( v2_lattice3(X0)
          & v1_lattice3(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_lattice3)).

fof(f140,plain,(
    ! [X1] :
      ( k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2)
      | ~ m1_subset_1(X1,k9_setfam_1(sK0))
      | ~ v2_lattice3(k2_yellow_1(k9_setfam_1(sK0))) ) ),
    inference(resolution,[],[f135,f90])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k12_lattice3(k2_yellow_1(X0),X2,X1) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f134,f55])).

fof(f55,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k12_lattice3(k2_yellow_1(X0),X2,X1) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f133,f51])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k12_lattice3(k2_yellow_1(X0),X2,X1) = k11_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f71,f56])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f75,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) != k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) != k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(definition_unfolding,[],[f41,f74,f42,f73,f42])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f72])).

fof(f65,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,
    ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f181,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(backward_demodulation,[],[f131,f176])).

fof(f176,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(subsumption_resolution,[],[f175,f89])).

fof(f175,plain,
    ( k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(subsumption_resolution,[],[f169,f90])).

fof(f169,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(resolution,[],[f167,f103])).

fof(f103,plain,(
    r2_hidden(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)),k9_setfam_1(sK0)) ),
    inference(resolution,[],[f100,f90])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k9_setfam_1(sK0))
      | r2_hidden(k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)),k9_setfam_1(sK0)) ) ),
    inference(resolution,[],[f99,f89])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ m1_subset_1(X2,k9_setfam_1(X0))
      | r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f98,f56])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k9_setfam_1(X0))
      | r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) ) ),
    inference(forward_demodulation,[],[f87,f56])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) ) ),
    inference(definition_unfolding,[],[f68,f73,f42,f42])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X0)
      | ~ m1_subset_1(X2,X0)
      | k10_lattice3(k2_yellow_1(X0),X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(forward_demodulation,[],[f166,f56])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k10_lattice3(k2_yellow_1(X0),X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(forward_demodulation,[],[f165,f56])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(subsumption_resolution,[],[f86,f62])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(k2_yellow_1(X0),X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f59,f73,f73])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k2_xboole_0(X1,X2),X0)
               => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_1)).

fof(f131,plain,(
    k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(resolution,[],[f128,f89])).

fof(f128,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(sK0))
      | k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) ) ),
    inference(subsumption_resolution,[],[f126,f94])).

fof(f94,plain,(
    ! [X0] : v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) ),
    inference(subsumption_resolution,[],[f93,f82])).

fof(f93,plain,(
    ! [X0] :
      ( v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | v2_struct_0(k2_yellow_1(k9_setfam_1(X0))) ) ),
    inference(subsumption_resolution,[],[f92,f51])).

fof(f92,plain,(
    ! [X0] :
      ( v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(k9_setfam_1(X0)))
      | v2_struct_0(k2_yellow_1(k9_setfam_1(X0))) ) ),
    inference(resolution,[],[f60,f83])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v3_lattice3(X0)
      | v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f126,plain,(
    ! [X1] :
      ( k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2)
      | ~ m1_subset_1(X1,k9_setfam_1(sK0))
      | ~ v1_lattice3(k2_yellow_1(k9_setfam_1(sK0))) ) ),
    inference(resolution,[],[f124,f90])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k13_lattice3(k2_yellow_1(X0),X2,X1) = k10_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v1_lattice3(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f123,f55])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k13_lattice3(k2_yellow_1(X0),X2,X1) = k10_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v1_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f122,f51])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k13_lattice3(k2_yellow_1(X0),X2,X1) = k10_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v1_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f70,f56])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (30152)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (30152)Refutation not found, incomplete strategy% (30152)------------------------------
% 0.20/0.41  % (30152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (30152)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (30152)Memory used [KB]: 10618
% 0.20/0.41  % (30152)Time elapsed: 0.004 s
% 0.20/0.41  % (30152)------------------------------
% 0.20/0.41  % (30152)------------------------------
% 0.20/0.45  % (30153)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.45  % (30153)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f182,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f181,f164])).
% 0.20/0.45  fof(f164,plain,(
% 0.20/0.45    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) != k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f163])).
% 0.20/0.45  fof(f163,plain,(
% 0.20/0.45    k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) != k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) | k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) != k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.20/0.45    inference(backward_demodulation,[],[f75,f160])).
% 0.20/0.45  fof(f160,plain,(
% 0.20/0.45    k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) = k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.20/0.45    inference(backward_demodulation,[],[f145,f155])).
% 0.20/0.45  fof(f155,plain,(
% 0.20/0.45    k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f154,f89])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.20/0.45    inference(backward_demodulation,[],[f77,f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,axiom,(
% 0.20/0.45    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.45  fof(f77,plain,(
% 0.20/0.45    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))),
% 0.20/0.45    inference(definition_unfolding,[],[f39,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,axiom,(
% 0.20/0.45    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.20/0.45    inference(cnf_transformation,[],[f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ((k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f33,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) => (? [X2] : ((k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2) | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ? [X2] : ((k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2) | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) => ((k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.20/0.45    inference(ennf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2))))),
% 0.20/0.45    inference(negated_conjecture,[],[f18])).
% 0.20/0.45  fof(f18,conjecture,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_yellow_1)).
% 0.20/0.45  fof(f154,plain,(
% 0.20/0.45    k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | ~m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.20/0.45    inference(subsumption_resolution,[],[f148,f90])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    m1_subset_1(sK2,k9_setfam_1(sK0))),
% 0.20/0.45    inference(backward_demodulation,[],[f76,f56])).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))),
% 0.20/0.45    inference(definition_unfolding,[],[f40,f42])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))),
% 0.20/0.45    inference(cnf_transformation,[],[f34])).
% 0.20/0.45  fof(f148,plain,(
% 0.20/0.45    ~m1_subset_1(sK2,k9_setfam_1(sK0)) | k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | ~m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.20/0.45    inference(resolution,[],[f138,f115])).
% 0.20/0.45  fof(f115,plain,(
% 0.20/0.45    r2_hidden(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)),k9_setfam_1(sK0))),
% 0.20/0.45    inference(resolution,[],[f112,f90])).
% 0.20/0.45  fof(f112,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,k9_setfam_1(sK0)) | r2_hidden(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X0)),k9_setfam_1(sK0))) )),
% 0.20/0.45    inference(resolution,[],[f111,f89])).
% 0.20/0.45  fof(f111,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | ~m1_subset_1(X2,k9_setfam_1(X0)) | r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0))) )),
% 0.20/0.45    inference(forward_demodulation,[],[f110,f56])).
% 0.20/0.45  fof(f110,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k9_setfam_1(X0)) | r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) )),
% 0.20/0.45    inference(forward_demodulation,[],[f88,f56])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f67,f74,f42,f42])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f64,f72])).
% 0.20/0.45  fof(f72,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f66,f69])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0,X1] : (! [X2] : ((r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.20/0.45    inference(ennf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l19_yellow_1)).
% 0.20/0.45  fof(f138,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X0) | ~m1_subset_1(X2,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.45    inference(forward_demodulation,[],[f137,f56])).
% 0.20/0.45  fof(f137,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) | ~r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.45    inference(forward_demodulation,[],[f136,f56])).
% 0.20/0.45  fof(f136,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) | ~r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f85,f62])).
% 0.20/0.45  fof(f62,plain,(
% 0.20/0.45    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.45    inference(rectify,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.45    inference(nnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.45  fof(f85,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) | ~r2_hidden(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f58,f74,f74])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,axiom,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k3_xboole_0(X1,X2),X0) => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).
% 0.20/0.45  fof(f145,plain,(
% 0.20/0.45    k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.20/0.45    inference(resolution,[],[f142,f89])).
% 0.20/0.45  fof(f142,plain,(
% 0.20/0.45    ( ! [X1] : (~m1_subset_1(X1,k9_setfam_1(sK0)) | k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f140,f97])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    ( ! [X0] : (v2_lattice3(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f96,f82])).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_struct_0(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f43,f42])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_struct_0(k3_yellow_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v4_orders_2(k3_yellow_1(X0)) & v3_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)) & ~v2_struct_0(k3_yellow_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    ( ! [X0] : (v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v2_struct_0(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f95,f51])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    ( ! [X0] : (v2_lattice3(k2_yellow_1(k9_setfam_1(X0))) | ~l1_orders_2(k2_yellow_1(k9_setfam_1(X0))) | v2_struct_0(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.45    inference(resolution,[],[f61,f83])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    ( ! [X0] : (v3_lattice3(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f49,f42])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X0] : (v3_lattice3(k3_yellow_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,axiom,(
% 0.20/0.45    ! [X0] : (v3_lattice3(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_yellow_1)).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    ( ! [X0] : (~v3_lattice3(X0) | v2_lattice3(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0] : ((v2_lattice3(X0) & v1_lattice3(X0)) | ~v3_lattice3(X0) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0] : (((v2_lattice3(X0) & v1_lattice3(X0)) | ~v3_lattice3(X0)) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => (v3_lattice3(X0) => (v2_lattice3(X0) & v1_lattice3(X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_lattice3)).
% 0.20/0.45  fof(f140,plain,(
% 0.20/0.45    ( ! [X1] : (k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) | ~m1_subset_1(X1,k9_setfam_1(sK0)) | ~v2_lattice3(k2_yellow_1(k9_setfam_1(sK0)))) )),
% 0.20/0.45    inference(resolution,[],[f135,f90])).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k12_lattice3(k2_yellow_1(X0),X2,X1) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f134,f55])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.20/0.45  fof(f134,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k12_lattice3(k2_yellow_1(X0),X2,X1) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f133,f51])).
% 0.20/0.45  fof(f133,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k12_lattice3(k2_yellow_1(X0),X2,X1) = k11_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(superposition,[],[f71,f56])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.45    inference(flattening,[],[f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) != k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK2)) != k12_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.20/0.45    inference(definition_unfolding,[],[f41,f74,f42,f73,f42])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f65,f72])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f34])).
% 0.20/0.45  fof(f181,plain,(
% 0.20/0.45    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.20/0.45    inference(backward_demodulation,[],[f131,f176])).
% 0.20/0.45  fof(f176,plain,(
% 0.20/0.45    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f175,f89])).
% 0.20/0.45  fof(f175,plain,(
% 0.20/0.45    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | ~m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.20/0.45    inference(subsumption_resolution,[],[f169,f90])).
% 0.20/0.45  fof(f169,plain,(
% 0.20/0.45    ~m1_subset_1(sK2,k9_setfam_1(sK0)) | k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | ~m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.20/0.45    inference(resolution,[],[f167,f103])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    r2_hidden(k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)),k9_setfam_1(sK0))),
% 0.20/0.45    inference(resolution,[],[f100,f90])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,k9_setfam_1(sK0)) | r2_hidden(k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)),k9_setfam_1(sK0))) )),
% 0.20/0.45    inference(resolution,[],[f99,f89])).
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | ~m1_subset_1(X2,k9_setfam_1(X0)) | r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0))) )),
% 0.20/0.45    inference(forward_demodulation,[],[f98,f56])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k9_setfam_1(X0)) | r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) )),
% 0.20/0.45    inference(forward_demodulation,[],[f87,f56])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f68,f73,f42,f42])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f27])).
% 0.20/0.45  fof(f167,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X0) | ~m1_subset_1(X2,X0) | k10_lattice3(k2_yellow_1(X0),X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.45    inference(forward_demodulation,[],[f166,f56])).
% 0.20/0.45  fof(f166,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k10_lattice3(k2_yellow_1(X0),X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.45    inference(forward_demodulation,[],[f165,f56])).
% 0.20/0.45  fof(f165,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k10_lattice3(k2_yellow_1(X0),X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f86,f62])).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k10_lattice3(k2_yellow_1(X0),X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~r2_hidden(k3_tarski(k2_enumset1(X1,X1,X1,X2)),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f59,f73,f73])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,axiom,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),X0) => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_1)).
% 0.20/0.45  fof(f131,plain,(
% 0.20/0.45    k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.20/0.45    inference(resolution,[],[f128,f89])).
% 0.20/0.45  fof(f128,plain,(
% 0.20/0.45    ( ! [X1] : (~m1_subset_1(X1,k9_setfam_1(sK0)) | k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f126,f94])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    ( ! [X0] : (v1_lattice3(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f93,f82])).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    ( ! [X0] : (v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | v2_struct_0(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f92,f51])).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    ( ! [X0] : (v1_lattice3(k2_yellow_1(k9_setfam_1(X0))) | ~l1_orders_2(k2_yellow_1(k9_setfam_1(X0))) | v2_struct_0(k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.45    inference(resolution,[],[f60,f83])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X0] : (~v3_lattice3(X0) | v1_lattice3(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f126,plain,(
% 0.20/0.45    ( ! [X1] : (k13_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),X1,sK2) | ~m1_subset_1(X1,k9_setfam_1(sK0)) | ~v1_lattice3(k2_yellow_1(k9_setfam_1(sK0)))) )),
% 0.20/0.45    inference(resolution,[],[f124,f90])).
% 0.20/0.45  fof(f124,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k13_lattice3(k2_yellow_1(X0),X2,X1) = k10_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v1_lattice3(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f123,f55])).
% 0.20/0.45  fof(f123,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k13_lattice3(k2_yellow_1(X0),X2,X1) = k10_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~v1_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f122,f51])).
% 0.20/0.45  fof(f122,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | k13_lattice3(k2_yellow_1(X0),X2,X1) = k10_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v1_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(superposition,[],[f70,f56])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.45    inference(flattening,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (30153)------------------------------
% 0.20/0.45  % (30153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (30153)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (30153)Memory used [KB]: 1663
% 0.20/0.45  % (30153)Time elapsed: 0.040 s
% 0.20/0.45  % (30153)------------------------------
% 0.20/0.45  % (30153)------------------------------
% 0.20/0.46  % (30140)Success in time 0.101 s
%------------------------------------------------------------------------------
