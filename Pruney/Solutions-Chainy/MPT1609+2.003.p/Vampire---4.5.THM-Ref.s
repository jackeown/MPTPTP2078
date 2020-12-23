%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 578 expanded)
%              Number of leaves         :   20 ( 195 expanded)
%              Depth                    :   17
%              Number of atoms          :  361 (1313 expanded)
%              Number of equality atoms :   79 ( 648 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f165])).

fof(f165,plain,(
    k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(superposition,[],[f73,f162])).

fof(f162,plain,(
    k2_xboole_0(sK1,sK2) = k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(forward_demodulation,[],[f160,f145])).

fof(f145,plain,(
    k2_xboole_0(sK1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(forward_demodulation,[],[f144,f76])).

fof(f76,plain,(
    ! [X0] : k3_lattice3(k1_lattice3(X0)) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f41,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f42,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f144,plain,(
    k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(subsumption_resolution,[],[f143,f115])).

fof(f115,plain,(
    ~ v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(resolution,[],[f111,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f111,plain,(
    r2_hidden(k2_xboole_0(sK1,sK1),k9_setfam_1(sK0)) ),
    inference(resolution,[],[f109,f93])).

fof(f93,plain,(
    m1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(backward_demodulation,[],[f75,f92])).

fof(f92,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(superposition,[],[f56,f76])).

fof(f56,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f75,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f38,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
      | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
    ( ? [X2] :
        ( ( k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2)
          | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0))) )
   => ( ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
        | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2)
            | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
           => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
              & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
            & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k9_setfam_1(sK0))
      | r2_hidden(k2_xboole_0(X0,sK1),k9_setfam_1(sK0)) ) ),
    inference(resolution,[],[f98,f93])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f96,f92])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(backward_demodulation,[],[f85,f92])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f70,f41,f41])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))
            & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l19_yellow_1)).

fof(f143,plain,
    ( k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(subsumption_resolution,[],[f142,f93])).

fof(f142,plain,
    ( k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(subsumption_resolution,[],[f131,f94])).

fof(f94,plain,(
    m1_subset_1(sK2,k9_setfam_1(sK0)) ),
    inference(backward_demodulation,[],[f74,f92])).

fof(f74,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0)))) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f39,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(resolution,[],[f88,f117])).

fof(f117,plain,(
    r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0)) ),
    inference(resolution,[],[f110,f93])).

fof(f110,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(sK0))
      | r2_hidden(k2_xboole_0(X1,sK2),k9_setfam_1(sK0)) ) ),
    inference(resolution,[],[f98,f94])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f87,f56])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f58,f56])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k2_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r2_hidden(k2_xboole_0(X1,X2),X0)
               => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_1)).

fof(f160,plain,(
    k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(resolution,[],[f155,f93])).

fof(f155,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(sK0))
      | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),X1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(sK0)),X1,sK2) ) ),
    inference(resolution,[],[f153,f94])).

fof(f153,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k9_setfam_1(X3))
      | k13_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k10_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4)
      | ~ m1_subset_1(X5,k9_setfam_1(X3)) ) ),
    inference(subsumption_resolution,[],[f152,f77])).

fof(f77,plain,(
    ! [X0] : v5_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f49,f41])).

fof(f49,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f152,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k9_setfam_1(X3))
      | k13_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k10_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4)
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X3))) ) ),
    inference(subsumption_resolution,[],[f151,f105])).

fof(f105,plain,(
    ! [X0] : v1_lattice3(k3_lattice3(k1_lattice3(X0))) ),
    inference(subsumption_resolution,[],[f104,f43])).

fof(f43,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).

fof(f104,plain,(
    ! [X0] :
      ( v1_lattice3(k3_lattice3(k1_lattice3(X0)))
      | v2_struct_0(k1_lattice3(X0)) ) ),
    inference(subsumption_resolution,[],[f103,f51])).

fof(f51,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(f103,plain,(
    ! [X0] :
      ( ~ l3_lattices(k1_lattice3(X0))
      | v1_lattice3(k3_lattice3(k1_lattice3(X0)))
      | v2_struct_0(k1_lattice3(X0)) ) ),
    inference(resolution,[],[f64,f53])).

fof(f53,plain,(
    ! [X0] : v10_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v10_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).

fof(f64,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v1_lattice3(k3_lattice3(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(k3_lattice3(X0))
        & v1_lattice3(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow_1)).

fof(f151,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k9_setfam_1(X3))
      | k13_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k10_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4)
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ v1_lattice3(k3_lattice3(k1_lattice3(X3)))
      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X3))) ) ),
    inference(subsumption_resolution,[],[f150,f82])).

fof(f82,plain,(
    ! [X0] : l1_orders_2(k3_lattice3(k1_lattice3(X0))) ),
    inference(definition_unfolding,[],[f55,f41])).

fof(f55,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f150,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k9_setfam_1(X3))
      | k13_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k10_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4)
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X3)))
      | ~ v1_lattice3(k3_lattice3(k1_lattice3(X3)))
      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X3))) ) ),
    inference(superposition,[],[f71,f92])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f73,plain,
    ( k2_xboole_0(sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)
    | k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(definition_unfolding,[],[f40,f68,f41,f41])).

fof(f68,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f40,plain,
    ( k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2)
    | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f199,plain,(
    k1_setfam_1(k2_tarski(sK1,sK2)) = k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(forward_demodulation,[],[f197,f189])).

fof(f189,plain,(
    k1_setfam_1(k2_tarski(sK1,sK2)) = k11_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(forward_demodulation,[],[f188,f76])).

fof(f188,plain,(
    k1_setfam_1(k2_tarski(sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) ),
    inference(subsumption_resolution,[],[f187,f115])).

fof(f187,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(subsumption_resolution,[],[f186,f93])).

fof(f186,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(subsumption_resolution,[],[f175,f94])).

fof(f175,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(sK0))
    | k1_setfam_1(k2_tarski(sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)
    | ~ m1_subset_1(sK1,k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(resolution,[],[f90,f125])).

fof(f125,plain,(
    r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k9_setfam_1(sK0)) ),
    inference(resolution,[],[f114,f93])).

fof(f114,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(sK0))
      | r2_hidden(k1_setfam_1(k2_tarski(X1,sK2)),k9_setfam_1(sK0)) ) ),
    inference(resolution,[],[f97,f94])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k9_setfam_1(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0)) ) ),
    inference(forward_demodulation,[],[f95,f92])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(backward_demodulation,[],[f86,f92])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) ) ),
    inference(definition_unfolding,[],[f69,f68,f41,f41])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f89,f56])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f84,f56])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f59,f68,f68])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)
              | ~ r2_hidden(k3_xboole_0(X1,X2),X0)
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
             => ( r2_hidden(k3_xboole_0(X1,X2),X0)
               => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_1)).

fof(f197,plain,(
    k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k11_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) ),
    inference(resolution,[],[f172,f93])).

fof(f172,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(sK0))
      | k12_lattice3(k3_lattice3(k1_lattice3(sK0)),X1,sK2) = k11_lattice3(k3_lattice3(k1_lattice3(sK0)),X1,sK2) ) ),
    inference(resolution,[],[f170,f94])).

fof(f170,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k9_setfam_1(X3))
      | k12_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k11_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4)
      | ~ m1_subset_1(X5,k9_setfam_1(X3)) ) ),
    inference(subsumption_resolution,[],[f169,f77])).

fof(f169,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k9_setfam_1(X3))
      | k12_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k11_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4)
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X3))) ) ),
    inference(subsumption_resolution,[],[f168,f108])).

fof(f108,plain,(
    ! [X0] : v2_lattice3(k3_lattice3(k1_lattice3(X0))) ),
    inference(subsumption_resolution,[],[f107,f43])).

fof(f107,plain,(
    ! [X0] :
      ( v2_lattice3(k3_lattice3(k1_lattice3(X0)))
      | v2_struct_0(k1_lattice3(X0)) ) ),
    inference(subsumption_resolution,[],[f106,f51])).

% (17520)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f106,plain,(
    ! [X0] :
      ( ~ l3_lattices(k1_lattice3(X0))
      | v2_lattice3(k3_lattice3(k1_lattice3(X0)))
      | v2_struct_0(k1_lattice3(X0)) ) ),
    inference(resolution,[],[f65,f53])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_lattice3(k3_lattice3(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f168,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k9_setfam_1(X3))
      | k12_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k11_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4)
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ v2_lattice3(k3_lattice3(k1_lattice3(X3)))
      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X3))) ) ),
    inference(subsumption_resolution,[],[f167,f82])).

fof(f167,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k9_setfam_1(X3))
      | k12_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k11_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4)
      | ~ m1_subset_1(X5,k9_setfam_1(X3))
      | ~ l1_orders_2(k3_lattice3(k1_lattice3(X3)))
      | ~ v2_lattice3(k3_lattice3(k1_lattice3(X3)))
      | ~ v5_orders_2(k3_lattice3(k1_lattice3(X3))) ) ),
    inference(superposition,[],[f72,f92])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:50:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (17517)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (17526)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (17516)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (17526)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f199,f165])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f164])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    k2_xboole_0(sK1,sK2) != k2_xboole_0(sK1,sK2) | k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.21/0.47    inference(superposition,[],[f73,f162])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    k2_xboole_0(sK1,sK2) = k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.21/0.47    inference(forward_demodulation,[],[f160,f145])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    k2_xboole_0(sK1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.21/0.47    inference(forward_demodulation,[],[f144,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0] : (k3_lattice3(k1_lattice3(X0)) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f42,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f143,f115])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ~v1_xboole_0(k9_setfam_1(sK0))),
% 0.21/0.47    inference(resolution,[],[f111,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(rectify,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    r2_hidden(k2_xboole_0(sK1,sK1),k9_setfam_1(sK0))),
% 0.21/0.47    inference(resolution,[],[f109,f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    m1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.21/0.47    inference(backward_demodulation,[],[f75,f92])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_lattice3(k1_lattice3(X0)))) )),
% 0.21/0.47    inference(superposition,[],[f56,f76])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.21/0.47    inference(definition_unfolding,[],[f38,f41])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ((k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f32,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) => (? [X2] : ((k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2) | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ? [X2] : ((k3_xboole_0(sK1,X2) != k12_lattice3(k3_yellow_1(sK0),sK1,X2) | k2_xboole_0(sK1,X2) != k13_lattice3(k3_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(sK0)))) => ((k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((k3_xboole_0(X1,X2) != k12_lattice3(k3_yellow_1(X0),X1,X2) | k2_xboole_0(X1,X2) != k13_lattice3(k3_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2))))),
% 0.21/0.47    inference(negated_conjecture,[],[f17])).
% 0.21/0.47  fof(f17,conjecture,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2) & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow_1)).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k9_setfam_1(sK0)) | r2_hidden(k2_xboole_0(X0,sK1),k9_setfam_1(sK0))) )),
% 0.21/0.47    inference(resolution,[],[f98,f93])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0)) | r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f96,f92])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f85,f92])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f70,f41,f41])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),k9_setfam_1(X0)) & r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l19_yellow_1)).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | v1_xboole_0(k9_setfam_1(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f142,f93])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | ~m1_subset_1(sK1,k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f131,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    m1_subset_1(sK2,k9_setfam_1(sK0))),
% 0.21/0.47    inference(backward_demodulation,[],[f74,f92])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    m1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(sK0))))),
% 0.21/0.47    inference(definition_unfolding,[],[f39,f41])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k9_setfam_1(sK0)) | k2_xboole_0(sK1,sK2) = k10_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | ~m1_subset_1(sK1,k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 0.21/0.47    inference(resolution,[],[f88,f117])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    r2_hidden(k2_xboole_0(sK1,sK2),k9_setfam_1(sK0))),
% 0.21/0.47    inference(resolution,[],[f110,f93])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X1] : (~m1_subset_1(X1,k9_setfam_1(sK0)) | r2_hidden(k2_xboole_0(X1,sK2),k9_setfam_1(sK0))) )),
% 0.21/0.47    inference(resolution,[],[f98,f94])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,X0) | k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f87,f56])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f58,f56])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k2_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k2_xboole_0(X1,X2),X0) => k2_xboole_0(X1,X2) = k10_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_1)).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.21/0.47    inference(resolution,[],[f155,f93])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ( ! [X1] : (~m1_subset_1(X1,k9_setfam_1(sK0)) | k13_lattice3(k3_lattice3(k1_lattice3(sK0)),X1,sK2) = k10_lattice3(k3_lattice3(k1_lattice3(sK0)),X1,sK2)) )),
% 0.21/0.47    inference(resolution,[],[f153,f94])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k9_setfam_1(X3)) | k13_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k10_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) | ~m1_subset_1(X5,k9_setfam_1(X3))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f152,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X0] : (v5_orders_2(k3_lattice3(k1_lattice3(X0)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f49,f41])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0] : (v5_orders_2(k3_yellow_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0] : (v5_orders_2(k3_yellow_1(X0)) & v4_orders_2(k3_yellow_1(X0)) & v3_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)) & ~v2_struct_0(k3_yellow_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k9_setfam_1(X3)) | k13_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k10_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~v5_orders_2(k3_lattice3(k1_lattice3(X3)))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f151,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ( ! [X0] : (v1_lattice3(k3_lattice3(k1_lattice3(X0)))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f104,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_struct_0(k1_lattice3(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : (v3_lattices(k1_lattice3(X0)) & ~v2_struct_0(k1_lattice3(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_lattice3)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X0] : (v1_lattice3(k3_lattice3(k1_lattice3(X0))) | v2_struct_0(k1_lattice3(X0))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f103,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (l3_lattices(k1_lattice3(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (l3_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattice3)).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ( ! [X0] : (~l3_lattices(k1_lattice3(X0)) | v1_lattice3(k3_lattice3(k1_lattice3(X0))) | v2_struct_0(k1_lattice3(X0))) )),
% 0.21/0.47    inference(resolution,[],[f64,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (v10_lattices(k1_lattice3(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (v10_lattices(k1_lattice3(X0)) & v3_lattices(k1_lattice3(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_lattice3)).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0] : (~v10_lattices(X0) | ~l3_lattices(X0) | v1_lattice3(k3_lattice3(X0)) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : ((v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : ((v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v2_lattice3(k3_lattice3(X0)) & v1_lattice3(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow_1)).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k9_setfam_1(X3)) | k13_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k10_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~v1_lattice3(k3_lattice3(k1_lattice3(X3))) | ~v5_orders_2(k3_lattice3(k1_lattice3(X3)))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f150,f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X0] : (l1_orders_2(k3_lattice3(k1_lattice3(X0)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f55,f41])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0] : (l1_orders_2(k3_yellow_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (l1_orders_2(k3_yellow_1(X0)) & v1_orders_2(k3_yellow_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_1)).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k9_setfam_1(X3)) | k13_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k10_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~l1_orders_2(k3_lattice3(k1_lattice3(X3))) | ~v1_lattice3(k3_lattice3(k1_lattice3(X3))) | ~v5_orders_2(k3_lattice3(k1_lattice3(X3)))) )),
% 0.21/0.48    inference(superposition,[],[f71,f92])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    k2_xboole_0(sK1,sK2) != k13_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) | k1_setfam_1(k2_tarski(sK1,sK2)) != k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.21/0.48    inference(definition_unfolding,[],[f40,f68,f41,f41])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    k3_xboole_0(sK1,sK2) != k12_lattice3(k3_yellow_1(sK0),sK1,sK2) | k2_xboole_0(sK1,sK2) != k13_lattice3(k3_yellow_1(sK0),sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    k1_setfam_1(k2_tarski(sK1,sK2)) = k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.21/0.48    inference(forward_demodulation,[],[f197,f189])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    k1_setfam_1(k2_tarski(sK1,sK2)) = k11_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.21/0.48    inference(forward_demodulation,[],[f188,f76])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    k1_setfam_1(k2_tarski(sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f187,f115])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    k1_setfam_1(k2_tarski(sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | v1_xboole_0(k9_setfam_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f186,f93])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    k1_setfam_1(k2_tarski(sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | ~m1_subset_1(sK1,k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f175,f94])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k9_setfam_1(sK0)) | k1_setfam_1(k2_tarski(sK1,sK2)) = k11_lattice3(k2_yellow_1(k9_setfam_1(sK0)),sK1,sK2) | ~m1_subset_1(sK1,k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f90,f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    r2_hidden(k1_setfam_1(k2_tarski(sK1,sK2)),k9_setfam_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f114,f93])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k9_setfam_1(sK0)) | r2_hidden(k1_setfam_1(k2_tarski(X1,sK2)),k9_setfam_1(sK0))) )),
% 0.21/0.48    inference(resolution,[],[f97,f94])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k9_setfam_1(X0)) | ~m1_subset_1(X1,k9_setfam_1(X0)) | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f95,f92])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 0.21/0.48    inference(backward_demodulation,[],[f86,f92])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X0)))) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(X0))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f69,f68,f41,f41])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k3_xboole_0(X1,X2),k9_setfam_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f89,f56])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f84,f56])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k11_lattice3(k2_yellow_1(X0),X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f59,f68,f68])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2) | ~r2_hidden(k3_xboole_0(X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r2_hidden(k3_xboole_0(X1,X2),X0) => k3_xboole_0(X1,X2) = k11_lattice3(k2_yellow_1(X0),X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_1)).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    k12_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2) = k11_lattice3(k3_lattice3(k1_lattice3(sK0)),sK1,sK2)),
% 0.21/0.48    inference(resolution,[],[f172,f93])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(X1,k9_setfam_1(sK0)) | k12_lattice3(k3_lattice3(k1_lattice3(sK0)),X1,sK2) = k11_lattice3(k3_lattice3(k1_lattice3(sK0)),X1,sK2)) )),
% 0.21/0.48    inference(resolution,[],[f170,f94])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k9_setfam_1(X3)) | k12_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k11_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) | ~m1_subset_1(X5,k9_setfam_1(X3))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f77])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k9_setfam_1(X3)) | k12_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k11_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~v5_orders_2(k3_lattice3(k1_lattice3(X3)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f168,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ( ! [X0] : (v2_lattice3(k3_lattice3(k1_lattice3(X0)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f107,f43])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0] : (v2_lattice3(k3_lattice3(k1_lattice3(X0))) | v2_struct_0(k1_lattice3(X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f106,f51])).
% 0.21/0.48  % (17520)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0] : (~l3_lattices(k1_lattice3(X0)) | v2_lattice3(k3_lattice3(k1_lattice3(X0))) | v2_struct_0(k1_lattice3(X0))) )),
% 0.21/0.48    inference(resolution,[],[f65,f53])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (~v10_lattices(X0) | ~l3_lattices(X0) | v2_lattice3(k3_lattice3(X0)) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k9_setfam_1(X3)) | k12_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k11_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~v2_lattice3(k3_lattice3(k1_lattice3(X3))) | ~v5_orders_2(k3_lattice3(k1_lattice3(X3)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f167,f82])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k9_setfam_1(X3)) | k12_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) = k11_lattice3(k3_lattice3(k1_lattice3(X3)),X5,X4) | ~m1_subset_1(X5,k9_setfam_1(X3)) | ~l1_orders_2(k3_lattice3(k1_lattice3(X3))) | ~v2_lattice3(k3_lattice3(k1_lattice3(X3))) | ~v5_orders_2(k3_lattice3(k1_lattice3(X3)))) )),
% 0.21/0.48    inference(superposition,[],[f72,f92])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17526)------------------------------
% 0.21/0.48  % (17526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17526)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17526)Memory used [KB]: 1791
% 0.21/0.48  % (17526)Time elapsed: 0.016 s
% 0.21/0.48  % (17526)------------------------------
% 0.21/0.48  % (17526)------------------------------
% 0.21/0.48  % (17503)Success in time 0.115 s
%------------------------------------------------------------------------------
