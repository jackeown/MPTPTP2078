%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 129 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :   28
%              Number of atoms          :  382 ( 635 expanded)
%              Number of equality atoms :   48 (  95 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(subsumption_resolution,[],[f196,f38])).

fof(f38,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))
    & r2_hidden(k1_xboole_0,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))
      & r2_hidden(k1_xboole_0,sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f196,plain,(
    ~ r2_hidden(k1_xboole_0,sK0) ),
    inference(resolution,[],[f181,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f181,plain,(
    ~ m1_subset_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f180,f37])).

fof(f37,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f180,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | v1_xboole_0(sK0) ),
    inference(trivial_inequality_removal,[],[f172])).

fof(f172,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f39,f171])).

fof(f171,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f169,f44])).

fof(f44,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f169,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(subsumption_resolution,[],[f168,f43])).

fof(f43,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f168,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f153,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f153,plain,(
    ! [X2] :
      ( ~ r2_lattice3(k2_yellow_1(X2),k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X2))
      | ~ m1_subset_1(k1_xboole_0,X2)
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f147,f43])).

fof(f147,plain,(
    ! [X2] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X2))
      | ~ r2_lattice3(k2_yellow_1(X2),k1_xboole_0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,X2)
      | v1_xboole_0(X2)
      | ~ l1_orders_2(k2_yellow_1(X2)) ) ),
    inference(superposition,[],[f146,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f146,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),X1)
      | ~ r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f144,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1))
      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f142,f44])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f141,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f42,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f80,f43])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f53,f44])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK1(X0,X1,X2))
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
        & r2_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f140,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f139,f41])).

fof(f41,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f138,f42])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ v5_orders_2(k2_yellow_1(X0))
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f135,f43])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0))
      | k1_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f85,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f64,f44])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f48,f44])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X2,sK1(X0,X2,X1))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | k1_yellow_0(X0,X1) = X2
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f84,f53])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r3_orders_2(X0,X2,sK1(X0,X2,X1))
      | ~ m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r3_orders_2(X0,X2,sK1(X0,X2,X1))
      | ~ m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f39,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (26671)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.44  % (26680)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.45  % (26671)Refutation not found, incomplete strategy% (26671)------------------------------
% 0.20/0.45  % (26671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (26671)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (26671)Memory used [KB]: 6012
% 0.20/0.45  % (26671)Time elapsed: 0.051 s
% 0.20/0.45  % (26671)------------------------------
% 0.20/0.45  % (26671)------------------------------
% 0.20/0.45  % (26680)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f197,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f196,f38])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    r2_hidden(k1_xboole_0,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k1_xboole_0,sK0) & ~v1_xboole_0(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k1_xboole_0,sK0) & ~v1_xboole_0(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 0.20/0.45    inference(flattening,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.45    inference(negated_conjecture,[],[f12])).
% 0.20/0.45  fof(f12,conjecture,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.20/0.45  fof(f196,plain,(
% 0.20/0.45    ~r2_hidden(k1_xboole_0,sK0)),
% 0.20/0.45    inference(resolution,[],[f181,f59])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.45  fof(f181,plain,(
% 0.20/0.45    ~m1_subset_1(k1_xboole_0,sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f180,f37])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ~v1_xboole_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  fof(f180,plain,(
% 0.20/0.45    ~m1_subset_1(k1_xboole_0,sK0) | v1_xboole_0(sK0)),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f172])).
% 0.20/0.45  fof(f172,plain,(
% 0.20/0.45    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,sK0) | v1_xboole_0(sK0)),
% 0.20/0.45    inference(superposition,[],[f39,f171])).
% 0.20/0.45  fof(f171,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f170])).
% 0.20/0.45  fof(f170,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(k1_xboole_0,X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(forward_demodulation,[],[f169,f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.45  fof(f169,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f168,f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.20/0.45  fof(f168,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(resolution,[],[f153,f50])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.20/0.45  fof(f153,plain,(
% 0.20/0.45    ( ! [X2] : (~r2_lattice3(k2_yellow_1(X2),k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X2)) | ~m1_subset_1(k1_xboole_0,X2) | v1_xboole_0(X2)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f147,f43])).
% 0.20/0.45  fof(f147,plain,(
% 0.20/0.45    ( ! [X2] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X2)) | ~r2_lattice3(k2_yellow_1(X2),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,X2) | v1_xboole_0(X2) | ~l1_orders_2(k2_yellow_1(X2))) )),
% 0.20/0.45    inference(superposition,[],[f146,f49])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.20/0.45  fof(f146,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 = k1_yellow_0(k2_yellow_1(X0),X1) | ~r2_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(resolution,[],[f144,f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.45  fof(f144,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~m1_subset_1(X2,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f143])).
% 0.20/0.45  fof(f143,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r2_lattice3(k2_yellow_1(X0),X1,X2) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~m1_subset_1(X2,X0) | ~r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(forward_demodulation,[],[f142,f44])).
% 0.20/0.45  fof(f142,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~m1_subset_1(X2,X0) | ~r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f141,f82])).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k1_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f81,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k1_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f80,f43])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k1_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(superposition,[],[f53,f44])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) & r2_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.45    inference(flattening,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.20/0.45    inference(rectify,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.20/0.45  fof(f141,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~m1_subset_1(X2,X0) | ~r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f140,f46])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.20/0.45    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.20/0.45  fof(f140,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~m1_subset_1(X2,X0) | ~r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f139,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f139,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~m1_subset_1(X2,X0) | ~r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f138,f42])).
% 0.20/0.45  fof(f138,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~v5_orders_2(k2_yellow_1(X0)) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~m1_subset_1(X2,X0) | ~r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f135,f43])).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0)) | k1_yellow_0(k2_yellow_1(X0),X1) = X2 | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~m1_subset_1(X2,X0) | ~r1_tarski(X2,sK1(k2_yellow_1(X0),X2,X1)) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(resolution,[],[f85,f65])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(forward_demodulation,[],[f64,f44])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(forward_demodulation,[],[f48,f44])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.20/0.45  fof(f85,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X2,sK1(X0,X2,X1)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | k1_yellow_0(X0,X1) = X2 | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f84,f53])).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~r3_orders_2(X0,X2,sK1(X0,X2,X1)) | ~m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0)) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f83])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_yellow_0(X0,X1) = X2 | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~r3_orders_2(X0,X2,sK1(X0,X2,X1)) | ~m1_subset_1(sK1(X0,X2,X1),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(resolution,[],[f55,f60])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,sK1(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f35])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f32])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (26680)------------------------------
% 0.20/0.45  % (26680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (26680)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (26680)Memory used [KB]: 1663
% 0.20/0.45  % (26680)Time elapsed: 0.056 s
% 0.20/0.45  % (26680)------------------------------
% 0.20/0.45  % (26680)------------------------------
% 0.20/0.45  % (26660)Success in time 0.103 s
%------------------------------------------------------------------------------
