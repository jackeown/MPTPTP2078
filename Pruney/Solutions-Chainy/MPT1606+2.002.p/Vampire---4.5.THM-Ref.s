%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 181 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   38
%              Number of atoms          :  488 ( 824 expanded)
%              Number of equality atoms :   53 ( 128 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f554,plain,(
    $false ),
    inference(subsumption_resolution,[],[f553,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0))
    & r2_hidden(k3_tarski(sK0),sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k3_tarski(X0),X0)
        & ~ v1_xboole_0(X0) )
   => ( k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0))
      & r2_hidden(k3_tarski(sK0),sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k3_tarski(X0),X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k3_tarski(X0),X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k3_tarski(X0),X0)
         => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f553,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f552,f81])).

fof(f81,plain,(
    m1_subset_1(k3_tarski(sK0),sK0) ),
    inference(subsumption_resolution,[],[f80,f42])).

fof(f80,plain,
    ( m1_subset_1(k3_tarski(sK0),sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    r2_hidden(k3_tarski(sK0),sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f552,plain,
    ( ~ m1_subset_1(k3_tarski(sK0),sK0)
    | v1_xboole_0(sK0) ),
    inference(trivial_inequality_removal,[],[f538])).

fof(f538,plain,
    ( k3_tarski(sK0) != k3_tarski(sK0)
    | ~ m1_subset_1(k3_tarski(sK0),sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f44,f477])).

fof(f477,plain,(
    ! [X4] :
      ( k3_tarski(X4) = k4_yellow_0(k2_yellow_1(X4))
      | ~ m1_subset_1(k3_tarski(X4),X4)
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f476,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f83,f47])).

fof(f47,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f54,f48])).

fof(f48,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattice3(X0,k1_xboole_0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f476,plain,(
    ! [X4] :
      ( k3_tarski(X4) = k4_yellow_0(k2_yellow_1(X4))
      | ~ m1_subset_1(k3_tarski(X4),X4)
      | v1_xboole_0(X4)
      | ~ r1_lattice3(k2_yellow_1(X4),k1_xboole_0,k3_tarski(X4)) ) ),
    inference(subsumption_resolution,[],[f449,f47])).

fof(f449,plain,(
    ! [X4] :
      ( k3_tarski(X4) = k4_yellow_0(k2_yellow_1(X4))
      | ~ m1_subset_1(k3_tarski(X4),X4)
      | v1_xboole_0(X4)
      | ~ r1_lattice3(k2_yellow_1(X4),k1_xboole_0,k3_tarski(X4))
      | ~ l1_orders_2(k2_yellow_1(X4)) ) ),
    inference(superposition,[],[f390,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_yellow_0)).

fof(f390,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1)
      | ~ m1_subset_1(k3_tarski(X0),X0)
      | v1_xboole_0(X0)
      | ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0)) ) ),
    inference(duplicate_literal_removal,[],[f389])).

fof(f389,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(k3_tarski(X0),X0)
      | k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1)
      | ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f388,f48])).

fof(f388,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tarski(X0),X0)
      | k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1)
      | ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0))
      | v1_xboole_0(X0)
      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tarski(X0),X0)
      | k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1)
      | ~ m1_subset_1(k3_tarski(X0),X0)
      | ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0))
      | v1_xboole_0(X0)
      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(forward_demodulation,[],[f386,f48])).

fof(f386,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1)
      | ~ m1_subset_1(k3_tarski(X0),X0)
      | ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(forward_demodulation,[],[f385,f48])).

fof(f385,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_tarski(X0),X0)
      | ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0))
      | v1_xboole_0(X0)
      | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(forward_demodulation,[],[f384,f48])).

fof(f384,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0))
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),X0)
      | v1_xboole_0(X0)
      | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(forward_demodulation,[],[f383,f48])).

fof(f383,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(u1_struct_0(k2_yellow_1(X0))))
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),X0)
      | v1_xboole_0(X0)
      | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(subsumption_resolution,[],[f382,f46])).

fof(f46,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f382,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(u1_struct_0(k2_yellow_1(X0))))
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),X0)
      | v1_xboole_0(X0)
      | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0)))
      | ~ v5_orders_2(k2_yellow_1(X0))
      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(subsumption_resolution,[],[f381,f47])).

fof(f381,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(u1_struct_0(k2_yellow_1(X0))))
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),X0)
      | v1_xboole_0(X0)
      | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0))
      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f374])).

fof(f374,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(u1_struct_0(k2_yellow_1(X0))))
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),X0)
      | v1_xboole_0(X0)
      | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(u1_struct_0(k2_yellow_1(X0))))
      | ~ m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0))
      | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(resolution,[],[f226,f119])).

fof(f119,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK1(X3,X5,X4),u1_struct_0(X3))
      | ~ r1_lattice3(X3,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | k2_yellow_0(X3,X4) = X5
      | v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(resolution,[],[f57,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X2) = X1
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK1(X0,X1,X2))
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

% (18320)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1(k2_yellow_1(X0),k3_tarski(X2),X1),X2)
      | ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X2))
      | ~ m1_subset_1(k3_tarski(X2),X0)
      | v1_xboole_0(X0)
      | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(X2) ) ),
    inference(resolution,[],[f133,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f131,f48])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f130,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k2_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r1_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f123,f46])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k2_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r1_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f121,f47])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k2_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r1_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f57,f48])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f129,f46])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ v5_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f128,f47])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f59,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f108,f48])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f106,f48])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f105,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f45,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f103,f47])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f69,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f73,f48])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f52,f48])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
      | k2_yellow_0(X0,X2) = X1
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f44,plain,(
    k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (18319)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (18321)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (18325)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (18326)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (18318)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (18318)Refutation not found, incomplete strategy% (18318)------------------------------
% 0.20/0.48  % (18318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18331)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (18317)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (18322)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (18327)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (18319)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (18318)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18318)Memory used [KB]: 10618
% 0.20/0.49  % (18318)Time elapsed: 0.072 s
% 0.20/0.49  % (18318)------------------------------
% 0.20/0.49  % (18318)------------------------------
% 0.20/0.49  % (18317)Refutation not found, incomplete strategy% (18317)------------------------------
% 0.20/0.49  % (18317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18317)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18317)Memory used [KB]: 6140
% 0.20/0.49  % (18317)Time elapsed: 0.048 s
% 0.20/0.49  % (18317)------------------------------
% 0.20/0.49  % (18317)------------------------------
% 0.20/0.49  % (18336)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f554,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f553,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~v1_xboole_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k3_tarski(sK0),sK0) & ~v1_xboole_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ? [X0] : (k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0) & ~v1_xboole_0(X0)) => (k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k3_tarski(sK0),sK0) & ~v1_xboole_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X0] : (k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0) & ~v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X0] : ((k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0)) & ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.49    inference(negated_conjecture,[],[f13])).
% 0.20/0.49  fof(f13,conjecture,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.20/0.49  fof(f553,plain,(
% 0.20/0.49    v1_xboole_0(sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f552,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    m1_subset_1(k3_tarski(sK0),sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f80,f42])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    m1_subset_1(k3_tarski(sK0),sK0) | v1_xboole_0(sK0)),
% 0.20/0.49    inference(resolution,[],[f64,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    r2_hidden(k3_tarski(sK0),sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.49  fof(f552,plain,(
% 0.20/0.49    ~m1_subset_1(k3_tarski(sK0),sK0) | v1_xboole_0(sK0)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f538])).
% 0.20/0.49  fof(f538,plain,(
% 0.20/0.49    k3_tarski(sK0) != k3_tarski(sK0) | ~m1_subset_1(k3_tarski(sK0),sK0) | v1_xboole_0(sK0)),
% 0.20/0.49    inference(superposition,[],[f44,f477])).
% 0.20/0.49  fof(f477,plain,(
% 0.20/0.49    ( ! [X4] : (k3_tarski(X4) = k4_yellow_0(k2_yellow_1(X4)) | ~m1_subset_1(k3_tarski(X4),X4) | v1_xboole_0(X4)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f476,f84])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f83,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.49    inference(superposition,[],[f54,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattice3(X0,k1_xboole_0,X1) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r1_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_lattice3(X0,k1_xboole_0,X1)))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.20/0.49  fof(f476,plain,(
% 0.20/0.49    ( ! [X4] : (k3_tarski(X4) = k4_yellow_0(k2_yellow_1(X4)) | ~m1_subset_1(k3_tarski(X4),X4) | v1_xboole_0(X4) | ~r1_lattice3(k2_yellow_1(X4),k1_xboole_0,k3_tarski(X4))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f449,f47])).
% 0.20/0.49  fof(f449,plain,(
% 0.20/0.49    ( ! [X4] : (k3_tarski(X4) = k4_yellow_0(k2_yellow_1(X4)) | ~m1_subset_1(k3_tarski(X4),X4) | v1_xboole_0(X4) | ~r1_lattice3(k2_yellow_1(X4),k1_xboole_0,k3_tarski(X4)) | ~l1_orders_2(k2_yellow_1(X4))) )),
% 0.20/0.49    inference(superposition,[],[f390,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0] : (k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (l1_orders_2(X0) => k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_yellow_0)).
% 0.20/0.49  fof(f390,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1) | ~m1_subset_1(k3_tarski(X0),X0) | v1_xboole_0(X0) | ~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f389])).
% 0.20/0.49  fof(f389,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(k3_tarski(X0),X0) | k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1) | ~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0)) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f388,f48])).
% 0.20/0.49  fof(f388,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(k3_tarski(X0),X0) | k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1) | ~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0)) | v1_xboole_0(X0) | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f387])).
% 0.20/0.49  fof(f387,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(k3_tarski(X0),X0) | k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1) | ~m1_subset_1(k3_tarski(X0),X0) | ~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0)) | v1_xboole_0(X0) | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f386,f48])).
% 0.20/0.49  fof(f386,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1) | ~m1_subset_1(k3_tarski(X0),X0) | ~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0)) | v1_xboole_0(X0) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f385,f48])).
% 0.20/0.49  fof(f385,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(k3_tarski(X0),X0) | ~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0)) | v1_xboole_0(X0) | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f384,f48])).
% 0.20/0.49  fof(f384,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0)) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),X0) | v1_xboole_0(X0) | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f383,f48])).
% 0.20/0.49  fof(f383,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),X0) | v1_xboole_0(X0) | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f382,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.20/0.49  fof(f382,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),X0) | v1_xboole_0(X0) | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0))) | ~v5_orders_2(k2_yellow_1(X0)) | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f381,f47])).
% 0.20/0.49  fof(f381,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),X0) | v1_xboole_0(X0) | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0)) | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f374])).
% 0.20/0.49  fof(f374,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),X0) | v1_xboole_0(X0) | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0))) | ~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(k3_tarski(u1_struct_0(k2_yellow_1(X0))),u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0)) | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(u1_struct_0(k2_yellow_1(X0)))) )),
% 0.20/0.49    inference(resolution,[],[f226,f119])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (r2_hidden(sK1(X3,X5,X4),u1_struct_0(X3)) | ~r1_lattice3(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v5_orders_2(X3) | k2_yellow_0(X3,X4) = X5 | v1_xboole_0(u1_struct_0(X3))) )),
% 0.20/0.49    inference(resolution,[],[f57,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | k2_yellow_0(X0,X2) = X1 | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,sK1(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  % (18320)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.20/0.49    inference(rectify,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(sK1(k2_yellow_1(X0),k3_tarski(X2),X1),X2) | ~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X2)) | ~m1_subset_1(k3_tarski(X2),X0) | v1_xboole_0(X0) | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(X2)) )),
% 0.20/0.49    inference(resolution,[],[f133,f68])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f131,f48])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,X0) | ~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f130,f124])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k2_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r1_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f123,f46])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k2_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r1_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f121,f47])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k2_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r1_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.49    inference(superposition,[],[f57,f48])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,X0) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f129,f46])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~v5_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f128,f47])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(resolution,[],[f59,f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f109])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f108,f48])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f107])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f106,f48])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f105,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f104,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f103,f47])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(resolution,[],[f69,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f73,f48])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f52,f48])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK1(X0,X1,X2),X1) | k2_yellow_0(X0,X2) = X1 | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (18319)------------------------------
% 0.20/0.49  % (18319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18319)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (18319)Memory used [KB]: 10874
% 0.20/0.49  % (18319)Time elapsed: 0.072 s
% 0.20/0.49  % (18319)------------------------------
% 0.20/0.49  % (18319)------------------------------
% 0.20/0.49  % (18329)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (18316)Success in time 0.129 s
%------------------------------------------------------------------------------
