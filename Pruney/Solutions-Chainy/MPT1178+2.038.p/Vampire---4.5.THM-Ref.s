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
% DateTime   : Thu Dec  3 13:10:30 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 292 expanded)
%              Number of leaves         :   17 (  93 expanded)
%              Depth                    :   23
%              Number of atoms          :  391 (1755 expanded)
%              Number of equality atoms :   26 ( 242 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f826,plain,(
    $false ),
    inference(subsumption_resolution,[],[f825,f267])).

fof(f267,plain,(
    m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(backward_demodulation,[],[f162,f264])).

fof(f264,plain,(
    k1_xboole_0 = sK4(sK0,sK1) ),
    inference(resolution,[],[f227,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f227,plain,(
    r1_tarski(sK4(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f223,f49])).

fof(f49,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
    ( ? [X1] :
        ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f223,plain,(
    r1_tarski(sK4(sK0,sK1),k3_tarski(k4_orders_2(sK0,sK1))) ),
    inference(resolution,[],[f208,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f208,plain,(
    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f207,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f207,plain,
    ( r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f44])).

fof(f44,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f206,plain,
    ( r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f205,f45])).

fof(f45,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f205,plain,
    ( r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f204,f46])).

fof(f46,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f204,plain,
    ( r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f203,f47])).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f203,plain,
    ( r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f200,f48])).

fof(f48,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f200,plain,
    ( r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f162,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f162,plain,(
    m2_orders_2(sK4(sK0,sK1),sK0,sK1) ),
    inference(subsumption_resolution,[],[f161,f43])).

fof(f161,plain,
    ( m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f160,f44])).

fof(f160,plain,
    ( m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f159,f45])).

fof(f159,plain,
    ( m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f46])).

fof(f158,plain,
    ( m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f135,f47])).

fof(f135,plain,
    ( m2_orders_2(sK4(sK0,sK1),sK0,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f48,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK4(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK4(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK4(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(f825,plain,(
    ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(forward_demodulation,[],[f822,f50])).

fof(f50,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f822,plain,(
    ~ m2_orders_2(k3_tarski(k1_xboole_0),sK0,sK1) ),
    inference(resolution,[],[f804,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f804,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK3(X3))
      | ~ m2_orders_2(k3_tarski(X3),sK0,sK1) ) ),
    inference(resolution,[],[f664,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f664,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | ~ m2_orders_2(k3_tarski(X0),sK0,sK1) ) ),
    inference(resolution,[],[f657,f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
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

fof(f657,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m2_orders_2(k3_tarski(X0),sK0,sK1) ) ),
    inference(condensation,[],[f656])).

fof(f656,plain,(
    ! [X8,X9] :
      ( ~ m2_orders_2(k3_tarski(X8),sK0,sK1)
      | ~ m2_orders_2(X9,sK0,sK1)
      | ~ v1_xboole_0(X8) ) ),
    inference(resolution,[],[f332,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f332,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1,X0),X1)
      | ~ m2_orders_2(k3_tarski(X1),sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f142,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f141,f43])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f140,f44])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f45])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f46])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f47])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f48,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.32  % Computer   : n012.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 18:23:07 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.18/0.40  % (32282)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.40  % (32291)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.42  % (32291)Refutation not found, incomplete strategy% (32291)------------------------------
% 0.18/0.42  % (32291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.42  % (32291)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.42  
% 0.18/0.42  % (32291)Memory used [KB]: 1663
% 0.18/0.42  % (32291)Time elapsed: 0.059 s
% 0.18/0.42  % (32291)------------------------------
% 0.18/0.42  % (32291)------------------------------
% 0.18/0.42  % (32282)Refutation found. Thanks to Tanya!
% 0.18/0.42  % SZS status Theorem for theBenchmark
% 0.18/0.42  % SZS output start Proof for theBenchmark
% 0.18/0.42  fof(f826,plain,(
% 0.18/0.42    $false),
% 0.18/0.42    inference(subsumption_resolution,[],[f825,f267])).
% 0.18/0.42  fof(f267,plain,(
% 0.18/0.42    m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.18/0.42    inference(backward_demodulation,[],[f162,f264])).
% 0.18/0.42  fof(f264,plain,(
% 0.18/0.42    k1_xboole_0 = sK4(sK0,sK1)),
% 0.18/0.42    inference(resolution,[],[f227,f52])).
% 0.18/0.42  fof(f52,plain,(
% 0.18/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f16])).
% 0.18/0.42  fof(f16,plain,(
% 0.18/0.42    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.18/0.42    inference(ennf_transformation,[],[f3])).
% 0.18/0.42  fof(f3,axiom,(
% 0.18/0.42    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.18/0.42  fof(f227,plain,(
% 0.18/0.42    r1_tarski(sK4(sK0,sK1),k1_xboole_0)),
% 0.18/0.42    inference(forward_demodulation,[],[f223,f49])).
% 0.18/0.42  fof(f49,plain,(
% 0.18/0.42    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.18/0.42    inference(cnf_transformation,[],[f30])).
% 0.18/0.42  fof(f30,plain,(
% 0.18/0.42    (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.18/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29,f28])).
% 0.18/0.42  fof(f28,plain,(
% 0.18/0.42    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.18/0.42    introduced(choice_axiom,[])).
% 0.18/0.42  fof(f29,plain,(
% 0.18/0.42    ? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.18/0.42    introduced(choice_axiom,[])).
% 0.18/0.42  fof(f15,plain,(
% 0.18/0.42    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.18/0.42    inference(flattening,[],[f14])).
% 0.18/0.42  fof(f14,plain,(
% 0.18/0.42    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f13])).
% 0.18/0.42  fof(f13,negated_conjecture,(
% 0.18/0.42    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.18/0.42    inference(negated_conjecture,[],[f12])).
% 0.18/0.42  fof(f12,conjecture,(
% 0.18/0.42    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.18/0.42  fof(f223,plain,(
% 0.18/0.42    r1_tarski(sK4(sK0,sK1),k3_tarski(k4_orders_2(sK0,sK1)))),
% 0.18/0.42    inference(resolution,[],[f208,f60])).
% 0.18/0.42  fof(f60,plain,(
% 0.18/0.42    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f21])).
% 0.18/0.42  fof(f21,plain,(
% 0.18/0.42    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.18/0.42    inference(ennf_transformation,[],[f4])).
% 0.18/0.42  fof(f4,axiom,(
% 0.18/0.42    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.18/0.42  fof(f208,plain,(
% 0.18/0.42    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1))),
% 0.18/0.42    inference(subsumption_resolution,[],[f207,f43])).
% 0.18/0.42  fof(f43,plain,(
% 0.18/0.42    ~v2_struct_0(sK0)),
% 0.18/0.42    inference(cnf_transformation,[],[f30])).
% 0.18/0.42  fof(f207,plain,(
% 0.18/0.42    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f206,f44])).
% 0.18/0.42  fof(f44,plain,(
% 0.18/0.42    v3_orders_2(sK0)),
% 0.18/0.42    inference(cnf_transformation,[],[f30])).
% 0.18/0.42  fof(f206,plain,(
% 0.18/0.42    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f205,f45])).
% 0.18/0.42  fof(f45,plain,(
% 0.18/0.42    v4_orders_2(sK0)),
% 0.18/0.42    inference(cnf_transformation,[],[f30])).
% 0.18/0.42  fof(f205,plain,(
% 0.18/0.42    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f204,f46])).
% 0.18/0.42  fof(f46,plain,(
% 0.18/0.42    v5_orders_2(sK0)),
% 0.18/0.42    inference(cnf_transformation,[],[f30])).
% 0.18/0.42  fof(f204,plain,(
% 0.18/0.42    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f203,f47])).
% 0.18/0.42  fof(f47,plain,(
% 0.18/0.42    l1_orders_2(sK0)),
% 0.18/0.42    inference(cnf_transformation,[],[f30])).
% 0.18/0.42  fof(f203,plain,(
% 0.18/0.42    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f200,f48])).
% 0.18/0.42  fof(f48,plain,(
% 0.18/0.42    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.18/0.42    inference(cnf_transformation,[],[f30])).
% 0.18/0.42  fof(f200,plain,(
% 0.18/0.42    r2_hidden(sK4(sK0,sK1),k4_orders_2(sK0,sK1)) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.18/0.42    inference(resolution,[],[f162,f66])).
% 0.18/0.42  fof(f66,plain,(
% 0.18/0.42    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_orders_2(X0,X1)) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.18/0.42    inference(equality_resolution,[],[f55])).
% 0.18/0.42  fof(f55,plain,(
% 0.18/0.42    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f34])).
% 0.18/0.42  fof(f34,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.18/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 0.18/0.42  fof(f33,plain,(
% 0.18/0.42    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.18/0.42    introduced(choice_axiom,[])).
% 0.18/0.42  fof(f32,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.18/0.42    inference(rectify,[],[f31])).
% 0.18/0.42  fof(f31,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.18/0.42    inference(nnf_transformation,[],[f20])).
% 0.18/0.42  fof(f20,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.18/0.42    inference(flattening,[],[f19])).
% 0.18/0.42  fof(f19,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f8])).
% 0.18/0.42  fof(f8,axiom,(
% 0.18/0.42    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.18/0.42  fof(f162,plain,(
% 0.18/0.42    m2_orders_2(sK4(sK0,sK1),sK0,sK1)),
% 0.18/0.42    inference(subsumption_resolution,[],[f161,f43])).
% 0.18/0.42  fof(f161,plain,(
% 0.18/0.42    m2_orders_2(sK4(sK0,sK1),sK0,sK1) | v2_struct_0(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f160,f44])).
% 0.18/0.42  fof(f160,plain,(
% 0.18/0.42    m2_orders_2(sK4(sK0,sK1),sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f159,f45])).
% 0.18/0.42  fof(f159,plain,(
% 0.18/0.42    m2_orders_2(sK4(sK0,sK1),sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f158,f46])).
% 0.18/0.42  fof(f158,plain,(
% 0.18/0.42    m2_orders_2(sK4(sK0,sK1),sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.18/0.42    inference(subsumption_resolution,[],[f135,f47])).
% 0.18/0.42  fof(f135,plain,(
% 0.18/0.42    m2_orders_2(sK4(sK0,sK1),sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.18/0.42    inference(resolution,[],[f48,f62])).
% 0.18/0.42  fof(f62,plain,(
% 0.18/0.42    ( ! [X0,X1] : (m2_orders_2(sK4(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f40])).
% 0.18/0.42  fof(f40,plain,(
% 0.18/0.42    ! [X0,X1] : (m2_orders_2(sK4(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.18/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f39])).
% 0.18/0.42  fof(f39,plain,(
% 0.18/0.42    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK4(X0,X1),X0,X1))),
% 0.18/0.42    introduced(choice_axiom,[])).
% 0.18/0.42  fof(f25,plain,(
% 0.18/0.42    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.18/0.42    inference(flattening,[],[f24])).
% 0.18/0.42  fof(f24,plain,(
% 0.18/0.42    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f9])).
% 0.18/0.42  fof(f9,axiom,(
% 0.18/0.42    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).
% 0.18/0.42  fof(f825,plain,(
% 0.18/0.42    ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.18/0.42    inference(forward_demodulation,[],[f822,f50])).
% 0.18/0.42  fof(f50,plain,(
% 0.18/0.42    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.18/0.42    inference(cnf_transformation,[],[f5])).
% 0.18/0.42  fof(f5,axiom,(
% 0.18/0.42    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.18/0.42  fof(f822,plain,(
% 0.18/0.42    ~m2_orders_2(k3_tarski(k1_xboole_0),sK0,sK1)),
% 0.18/0.42    inference(resolution,[],[f804,f51])).
% 0.18/0.42  fof(f51,plain,(
% 0.18/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f2])).
% 0.18/0.42  fof(f2,axiom,(
% 0.18/0.42    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.42  fof(f804,plain,(
% 0.18/0.42    ( ! [X3] : (~r1_tarski(X3,sK3(X3)) | ~m2_orders_2(k3_tarski(X3),sK0,sK1)) )),
% 0.18/0.42    inference(resolution,[],[f664,f65])).
% 0.18/0.42  fof(f65,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f27])).
% 0.18/0.42  fof(f27,plain,(
% 0.18/0.42    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.18/0.42    inference(ennf_transformation,[],[f7])).
% 0.18/0.42  fof(f7,axiom,(
% 0.18/0.42    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.18/0.42  fof(f664,plain,(
% 0.18/0.42    ( ! [X0] : (r2_hidden(sK3(X0),X0) | ~m2_orders_2(k3_tarski(X0),sK0,sK1)) )),
% 0.18/0.42    inference(resolution,[],[f657,f59])).
% 0.18/0.42  fof(f59,plain,(
% 0.18/0.42    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f38])).
% 0.18/0.42  fof(f38,plain,(
% 0.18/0.42    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 0.18/0.42  fof(f37,plain,(
% 0.18/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.18/0.42    introduced(choice_axiom,[])).
% 0.18/0.42  fof(f36,plain,(
% 0.18/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.42    inference(rectify,[],[f35])).
% 0.18/0.42  fof(f35,plain,(
% 0.18/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.18/0.42    inference(nnf_transformation,[],[f1])).
% 0.18/0.42  fof(f1,axiom,(
% 0.18/0.42    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.42  fof(f657,plain,(
% 0.18/0.42    ( ! [X0] : (~v1_xboole_0(X0) | ~m2_orders_2(k3_tarski(X0),sK0,sK1)) )),
% 0.18/0.42    inference(condensation,[],[f656])).
% 0.18/0.42  fof(f656,plain,(
% 0.18/0.42    ( ! [X8,X9] : (~m2_orders_2(k3_tarski(X8),sK0,sK1) | ~m2_orders_2(X9,sK0,sK1) | ~v1_xboole_0(X8)) )),
% 0.18/0.42    inference(resolution,[],[f332,f58])).
% 0.18/0.42  fof(f58,plain,(
% 0.18/0.42    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f38])).
% 0.18/0.42  fof(f332,plain,(
% 0.18/0.42    ( ! [X0,X1] : (r2_hidden(sK5(X1,X0),X1) | ~m2_orders_2(k3_tarski(X1),sK0,sK1) | ~m2_orders_2(X0,sK0,sK1)) )),
% 0.18/0.42    inference(resolution,[],[f142,f63])).
% 0.18/0.42  fof(f63,plain,(
% 0.18/0.42    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f42])).
% 0.18/0.42  fof(f42,plain,(
% 0.18/0.42    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | (~r1_xboole_0(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.18/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f41])).
% 0.18/0.42  fof(f41,plain,(
% 0.18/0.42    ! [X1,X0] : (? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)) => (~r1_xboole_0(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.18/0.42    introduced(choice_axiom,[])).
% 0.18/0.42  fof(f26,plain,(
% 0.18/0.42    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f6])).
% 0.18/0.42  fof(f6,axiom,(
% 0.18/0.42    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).
% 0.18/0.42  fof(f142,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1)) )),
% 0.18/0.42    inference(subsumption_resolution,[],[f141,f43])).
% 0.18/0.42  fof(f141,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | v2_struct_0(sK0)) )),
% 0.18/0.42    inference(subsumption_resolution,[],[f140,f44])).
% 0.18/0.42  fof(f140,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.18/0.42    inference(subsumption_resolution,[],[f139,f45])).
% 0.18/0.42  fof(f139,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.18/0.42    inference(subsumption_resolution,[],[f138,f46])).
% 0.18/0.42  fof(f138,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.18/0.42    inference(subsumption_resolution,[],[f131,f47])).
% 0.18/0.42  fof(f131,plain,(
% 0.18/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.18/0.42    inference(resolution,[],[f48,f53])).
% 0.18/0.42  fof(f53,plain,(
% 0.18/0.42    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.18/0.42    inference(cnf_transformation,[],[f18])).
% 0.18/0.42  fof(f18,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.18/0.42    inference(flattening,[],[f17])).
% 0.18/0.42  fof(f17,plain,(
% 0.18/0.42    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.18/0.42    inference(ennf_transformation,[],[f11])).
% 0.18/0.42  fof(f11,axiom,(
% 0.18/0.42    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.18/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_orders_2)).
% 0.18/0.42  % SZS output end Proof for theBenchmark
% 0.18/0.42  % (32282)------------------------------
% 0.18/0.42  % (32282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.42  % (32282)Termination reason: Refutation
% 0.18/0.42  
% 0.18/0.42  % (32282)Memory used [KB]: 1918
% 0.18/0.42  % (32282)Time elapsed: 0.059 s
% 0.18/0.42  % (32282)------------------------------
% 0.18/0.42  % (32282)------------------------------
% 0.18/0.42  % (32275)Success in time 0.089 s
%------------------------------------------------------------------------------
