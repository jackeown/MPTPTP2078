%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 467 expanded)
%              Number of leaves         :   11 ( 150 expanded)
%              Depth                    :   31
%              Number of atoms          :  434 (3060 expanded)
%              Number of equality atoms :   57 ( 492 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f101,f36])).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f101,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f100,f66])).

fof(f66,plain,(
    k1_xboole_0 = sK4(sK0,sK1) ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(f65,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f64,f30])).

fof(f30,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f63,f31])).

fof(f31,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f62,f32])).

fof(f32,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f61,f33])).

fof(f33,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f60,f34])).

fof(f34,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f59,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK4(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK4(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK4(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(f59,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f58,f29])).

fof(f58,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | v2_struct_0(sK0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f57,f30])).

fof(f57,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f56,f31])).

fof(f56,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f55,f32])).

fof(f55,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f54,f33])).

fof(f54,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f53,f34])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f46,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
      | k1_xboole_0 = X0 ) ),
    inference(trivial_inequality_removal,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k4_orders_2(sK0,sK1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f37,f35])).

fof(f35,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK2(X0),X0)
          & k1_xboole_0 != sK2(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK2(X0),X0)
        & k1_xboole_0 != sK2(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ m2_orders_2(X4,X0,X1)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK3(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK3(X0,X1,X2),X0,X1)
                    | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK3(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( m2_orders_2(sK3(X0,X1,X2),X0,X1)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(f100,plain,(
    ~ r1_xboole_0(k1_xboole_0,sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f99,f29])).

fof(f99,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK4(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f98,f30])).

fof(f98,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK4(sK0,sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f97,f31])).

fof(f97,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK4(sK0,sK1))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f96,f32])).

fof(f96,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK4(sK0,sK1))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f95,f33])).

fof(f95,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK4(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f93,f34])).

fof(f93,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK4(sK0,sK1))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f92,f45])).

fof(f92,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f91,f66])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(sK4(sK0,sK1),X0) ) ),
    inference(subsumption_resolution,[],[f90,f29])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(sK4(sK0,sK1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(sK4(sK0,sK1),X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f88,f31])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(sK4(sK0,sK1),X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f32])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(sK4(sK0,sK1),X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f33])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(sK4(sK0,sK1),X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f84,f34])).

fof(f84,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(sK4(sK0,sK1),X0)
      | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f83,f45])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(subsumption_resolution,[],[f82,f29])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ r1_xboole_0(X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f30])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ r1_xboole_0(X1,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f80,f31])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ r1_xboole_0(X1,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ r1_xboole_0(X1,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ r1_xboole_0(X1,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f40,f34])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ r1_xboole_0(X2,X3)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (5796)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.45  % (5796)Refutation not found, incomplete strategy% (5796)------------------------------
% 0.20/0.45  % (5796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (5796)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (5796)Memory used [KB]: 1535
% 0.20/0.45  % (5796)Time elapsed: 0.044 s
% 0.20/0.45  % (5796)------------------------------
% 0.20/0.45  % (5796)------------------------------
% 0.20/0.46  % (5793)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (5791)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (5801)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (5784)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (5801)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f101,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.47    inference(forward_demodulation,[],[f100,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    k1_xboole_0 = sK4(sK0,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f65,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ~v2_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f19,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    k1_xboole_0 = sK4(sK0,sK1) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f64,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    v3_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    k1_xboole_0 = sK4(sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f63,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    v4_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    k1_xboole_0 = sK4(sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f62,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    v5_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    k1_xboole_0 = sK4(sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f61,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    l1_orders_2(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    k1_xboole_0 = sK4(sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f60,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    k1_xboole_0 = sK4(sK0,sK1) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f59,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m2_orders_2(sK4(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : (m2_orders_2(sK4(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK4(X0,X1),X0,X1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f58,f29])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | v2_struct_0(sK0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f57,f30])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f56,f31])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f55,f32])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f54,f33])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f53,f34])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(resolution,[],[f46,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k4_orders_2(sK0,sK1)) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(superposition,[],[f37,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : (((r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK2(X0),X0) & k1_xboole_0 != sK2(X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 0.20/0.48    inference(rectify,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_orders_2(X0,X1)) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK3(X0,X1,X2),X0,X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (m2_orders_2(sK3(X0,X1,X2),X0,X1) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK3(X0,X1,X2),X0,X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (m2_orders_2(sK3(X0,X1,X2),X0,X1) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(rectify,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_xboole_0,sK4(sK0,sK1))),
% 0.20/0.48    inference(subsumption_resolution,[],[f99,f29])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_xboole_0,sK4(sK0,sK1)) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f98,f30])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_xboole_0,sK4(sK0,sK1)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f97,f31])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_xboole_0,sK4(sK0,sK1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f96,f32])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_xboole_0,sK4(sK0,sK1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f95,f33])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_xboole_0,sK4(sK0,sK1)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f93,f34])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ~r1_xboole_0(k1_xboole_0,sK4(sK0,sK1)) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f92,f45])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f91,f66])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(sK4(sK0,sK1),X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f90,f29])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(sK4(sK0,sK1),X0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f89,f30])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(sK4(sK0,sK1),X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f88,f31])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(sK4(sK0,sK1),X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f87,f32])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(sK4(sK0,sK1),X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f86,f33])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(sK4(sK0,sK1),X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f84,f34])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(sK4(sK0,sK1),X0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(resolution,[],[f83,f45])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~r1_xboole_0(X1,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f82,f29])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,X0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f81,f30])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f80,f31])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f79,f32])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f78,f33])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | ~r1_xboole_0(X1,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(resolution,[],[f40,f34])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~r1_xboole_0(X2,X3) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (5801)------------------------------
% 0.20/0.48  % (5801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (5801)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (5801)Memory used [KB]: 1663
% 0.20/0.48  % (5801)Time elapsed: 0.071 s
% 0.20/0.48  % (5801)------------------------------
% 0.20/0.48  % (5801)------------------------------
% 0.20/0.48  % (5781)Success in time 0.124 s
%------------------------------------------------------------------------------
