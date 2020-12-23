%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 (2531 expanded)
%              Number of leaves         :   17 ( 699 expanded)
%              Depth                    :   28
%              Number of atoms          :  467 (12532 expanded)
%              Number of equality atoms :   54 (2037 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(global_subsumption,[],[f49,f414])).

fof(f414,plain,(
    k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f413,f88])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f61,f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f51,f50])).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f413,plain,(
    ! [X0] : ~ r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),X0) ),
    inference(global_subsumption,[],[f189,f256,f411])).

fof(f411,plain,(
    ! [X0] :
      ( r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))
      | ~ r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),X0)
      | ~ sP0(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) ) ),
    inference(superposition,[],[f200,f258])).

fof(f258,plain,(
    ! [X1] : sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,X1,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(resolution,[],[f256,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK5(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,sK4(X0,X1,X3),X3)
              & r2_hidden(sK4(X0,X1,X3),X1)
              & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,X6,sK5(X0,X1,X2))
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK5(X0,X1,X2) = X2
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).

fof(f41,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X4,X3)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,sK4(X0,X1,X3),X3)
        & r2_hidden(sK4(X0,X1,X3),X1)
        & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X6,X5)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,X6,sK5(X0,X1,X2))
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK5(X0,X1,X2) = X2
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X0,X4,X3)
                & r2_hidden(X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_orders_2(X0,X6,X5)
                | ~ r2_hidden(X6,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            & X2 = X5
            & m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X1,X4,X3)
                & r2_hidden(X4,X2)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X4,X3)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f200,plain,(
    ! [X10,X9] :
      ( r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),sK5(sK2,X9,X10))
      | ~ r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),X9)
      | ~ sP0(sK2,X9,X10) ) ),
    inference(resolution,[],[f190,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,X1)
      | r2_orders_2(sK2,X0,sK5(sK2,X1,X2))
      | ~ sP0(sK2,X1,X2) ) ),
    inference(superposition,[],[f66,f78])).

fof(f78,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f52,f77])).

fof(f77,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f66,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | r2_orders_2(X0,X6,sK5(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f190,plain,(
    m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(global_subsumption,[],[f179,f185])).

fof(f185,plain,
    ( m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(superposition,[],[f83,f180])).

fof(f180,plain,(
    sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(resolution,[],[f179,f65])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(sK2,X0,X1),k2_struct_0(sK2))
      | ~ sP0(sK2,X0,X1) ) ),
    inference(superposition,[],[f64,f78])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f179,plain,(
    sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(global_subsumption,[],[f49,f176])).

fof(f176,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f173,f88])).

fof(f173,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_orders_2(sK2,k2_struct_0(sK2)))
      | sP0(sK2,k2_struct_0(sK2),X2) ) ),
    inference(global_subsumption,[],[f131,f170])).

fof(f170,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_orders_2(sK2,k2_struct_0(sK2)))
      | sP0(sK2,k2_struct_0(sK2),X2)
      | ~ sP1(X2,k2_struct_0(sK2),sK2) ) ),
    inference(superposition,[],[f62,f165])).

fof(f165,plain,(
    k1_orders_2(sK2,k2_struct_0(sK2)) = a_2_0_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f164,f76])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) ) ),
    inference(global_subsumption,[],[f48,f46,f45,f44,f163])).

fof(f163,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(forward_demodulation,[],[f162,f78])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f57,f47])).

fof(f47,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(f44,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(X2,X1))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f131,plain,(
    ! [X0] : sP1(X0,k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f130,f76])).

% (11059)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(global_subsumption,[],[f48,f46,f45,f44,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(forward_demodulation,[],[f128,f78])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f70,f47])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sP1(X0,X2,X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f27,f29,f28])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f256,plain,(
    ! [X0] : sP0(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(global_subsumption,[],[f179,f190,f254])).

fof(f254,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
      | sP0(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))
      | ~ sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) ) ),
    inference(superposition,[],[f251,f180])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(sK2,k2_struct_0(sK2),X0),k2_struct_0(sK2))
      | sP0(sK2,X1,sK5(sK2,k2_struct_0(sK2),X0))
      | ~ sP0(sK2,k2_struct_0(sK2),X0) ) ),
    inference(global_subsumption,[],[f80,f250])).

fof(f250,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK5(sK2,k2_struct_0(sK2),X0),k2_struct_0(sK2))
      | sP0(sK2,X1,sK5(sK2,k2_struct_0(sK2),X0))
      | v1_xboole_0(k2_struct_0(sK2))
      | ~ sP0(sK2,k2_struct_0(sK2),X0) ) ),
    inference(forward_demodulation,[],[f249,f78])).

fof(f249,plain,(
    ! [X0,X1] :
      ( sP0(sK2,X1,sK5(sK2,k2_struct_0(sK2),X0))
      | v1_xboole_0(k2_struct_0(sK2))
      | ~ sP0(sK2,k2_struct_0(sK2),X0)
      | ~ m1_subset_1(sK5(sK2,u1_struct_0(sK2),X0),u1_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f248,f78])).

fof(f248,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_struct_0(sK2))
      | ~ sP0(sK2,k2_struct_0(sK2),X0)
      | sP0(sK2,X1,sK5(sK2,u1_struct_0(sK2),X0))
      | ~ m1_subset_1(sK5(sK2,u1_struct_0(sK2),X0),u1_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f247,f78])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK2,k2_struct_0(sK2),X0)
      | v1_xboole_0(u1_struct_0(sK2))
      | sP0(sK2,X1,sK5(sK2,u1_struct_0(sK2),X0))
      | ~ m1_subset_1(sK5(sK2,u1_struct_0(sK2),X0),u1_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f246,f78])).

fof(f246,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK2,u1_struct_0(sK2),X0)
      | v1_xboole_0(u1_struct_0(sK2))
      | sP0(sK2,X1,sK5(sK2,u1_struct_0(sK2),X0))
      | ~ m1_subset_1(sK5(sK2,u1_struct_0(sK2),X0),u1_struct_0(sK2)) ) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK2,u1_struct_0(sK2),X0)
      | v1_xboole_0(u1_struct_0(sK2))
      | sP0(sK2,X1,sK5(sK2,u1_struct_0(sK2),X0))
      | sP0(sK2,X1,sK5(sK2,u1_struct_0(sK2),X0))
      | ~ m1_subset_1(sK5(sK2,u1_struct_0(sK2),X0),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f231,f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))
      | sP0(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f231,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(sK4(sK2,X2,sK5(sK2,X3,X4)),X3)
      | ~ sP0(sK2,X3,X4)
      | v1_xboole_0(X3)
      | sP0(sK2,X2,sK5(sK2,X3,X4)) ) ),
    inference(resolution,[],[f228,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(sK2,X2,sK5(sK2,X0,X1)),X0)
      | sP0(sK2,X2,sK5(sK2,X0,X1))
      | ~ sP0(sK2,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(sK2,X0,X1)
      | sP0(sK2,X2,sK5(sK2,X0,X1))
      | ~ r2_hidden(sK4(sK2,X2,sK5(sK2,X0,X1)),X0)
      | ~ sP0(sK2,X0,X1) ) ),
    inference(resolution,[],[f224,f83])).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK5(sK2,X1,X2),k2_struct_0(sK2))
      | ~ sP0(sK2,X1,X2)
      | sP0(sK2,X0,sK5(sK2,X1,X2))
      | ~ r2_hidden(sK4(sK2,X0,sK5(sK2,X1,X2)),X1) ) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(sK2,X0,sK5(sK2,X1,X2)),X1)
      | ~ sP0(sK2,X1,X2)
      | sP0(sK2,X0,sK5(sK2,X1,X2))
      | ~ m1_subset_1(sK5(sK2,X1,X2),k2_struct_0(sK2))
      | sP0(sK2,X0,sK5(sK2,X1,X2))
      | ~ sP0(sK2,X1,X2) ) ),
    inference(resolution,[],[f122,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_orders_2(X0,sK4(X0,X1,sK5(X0,X2,X3)),sK5(X0,X2,X3))
      | sP0(X0,X1,sK5(X0,X2,X3))
      | ~ sP0(X0,X2,X3) ) ),
    inference(resolution,[],[f72,f64])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_orders_2(X0,sK4(X0,X1,X3),X3)
      | sP0(X0,X1,X3) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_orders_2(X0,sK4(X0,X1,X3),X3)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f122,plain,(
    ! [X4,X2,X5,X3] :
      ( r2_orders_2(sK2,sK4(sK2,X2,X3),sK5(sK2,X4,X5))
      | ~ r2_hidden(sK4(sK2,X2,X3),X4)
      | ~ sP0(sK2,X4,X5)
      | sP0(sK2,X2,X3)
      | ~ m1_subset_1(X3,k2_struct_0(sK2)) ) ),
    inference(resolution,[],[f120,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(sK2,X0,X1),k2_struct_0(sK2))
      | sP0(sK2,X0,X1)
      | ~ m1_subset_1(X1,k2_struct_0(sK2)) ) ),
    inference(superposition,[],[f74,f78])).

fof(f80,plain,(
    ~ v1_xboole_0(k2_struct_0(sK2)) ),
    inference(global_subsumption,[],[f44,f77,f79])).

fof(f79,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f58,f78])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f189,plain,(
    ~ r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(global_subsumption,[],[f179,f184])).

% (11051)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f184,plain,
    ( ~ r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))
    | ~ sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(superposition,[],[f84,f180])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(sK2,sK5(sK2,X0,X1),sK5(sK2,X0,X1))
      | ~ sP0(sK2,X0,X1) ) ),
    inference(resolution,[],[f83,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_orders_2(sK2,X0,X0) ) ),
    inference(forward_demodulation,[],[f81,f78])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_orders_2(sK2,X0,X0) ) ),
    inference(resolution,[],[f75,f48])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f49,plain,(
    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:17:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (11039)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.45  % (11050)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (11049)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.49  % (11050)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(global_subsumption,[],[f49,f414])).
% 0.21/0.49  fof(f414,plain,(
% 0.21/0.49    k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.49    inference(resolution,[],[f413,f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(X0,X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(resolution,[],[f61,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f51,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 0.21/0.49  fof(f413,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),X0)) )),
% 0.21/0.49    inference(global_subsumption,[],[f189,f256,f411])).
% 0.21/0.49  fof(f411,plain,(
% 0.21/0.49    ( ! [X0] : (r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) | ~r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),X0) | ~sP0(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))) )),
% 0.21/0.49    inference(superposition,[],[f200,f258])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    ( ! [X1] : (sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,X1,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))) )),
% 0.21/0.49    inference(resolution,[],[f256,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK5(X0,X1,X2) = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,sK4(X0,X1,X3),X3) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,X6,sK5(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,sK4(X0,X1,X3),X3) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,X6,sK5(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.49    inference(rectify,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    ( ! [X10,X9] : (r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),sK5(sK2,X9,X10)) | ~r2_hidden(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),X9) | ~sP0(sK2,X9,X10)) )),
% 0.21/0.49    inference(resolution,[],[f190,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,X1) | r2_orders_2(sK2,X0,sK5(sK2,X1,X2)) | ~sP0(sK2,X1,X2)) )),
% 0.21/0.49    inference(superposition,[],[f66,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.21/0.49    inference(resolution,[],[f52,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    l1_struct_0(sK2)),
% 0.21/0.49    inference(resolution,[],[f53,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    l1_orders_2(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X1] : (~m1_subset_1(X6,u1_struct_0(X0)) | ~r2_hidden(X6,X1) | r2_orders_2(X0,X6,sK5(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.50    inference(global_subsumption,[],[f179,f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.50    inference(superposition,[],[f83,f180])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.50    inference(resolution,[],[f179,f65])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(sK5(sK2,X0,X1),k2_struct_0(sK2)) | ~sP0(sK2,X0,X1)) )),
% 0.21/0.50    inference(superposition,[],[f64,f78])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.50    inference(global_subsumption,[],[f49,f176])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = k1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f173,f88])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,k1_orders_2(sK2,k2_struct_0(sK2))) | sP0(sK2,k2_struct_0(sK2),X2)) )),
% 0.21/0.50    inference(global_subsumption,[],[f131,f170])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,k1_orders_2(sK2,k2_struct_0(sK2))) | sP0(sK2,k2_struct_0(sK2),X2) | ~sP1(X2,k2_struct_0(sK2),sK2)) )),
% 0.21/0.50    inference(superposition,[],[f62,f165])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    k1_orders_2(sK2,k2_struct_0(sK2)) = a_2_0_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f164,f76])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0)) )),
% 0.21/0.50    inference(global_subsumption,[],[f48,f46,f45,f44,f163])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_orders_2(sK2) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f162,f78])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | k1_orders_2(sK2,X0) = a_2_0_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(resolution,[],[f57,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    v5_orders_2(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ~v2_struct_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v3_orders_2(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    v4_orders_2(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(X2,X1)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 0.21/0.50    inference(rectify,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ( ! [X0] : (sP1(X0,k2_struct_0(sK2),sK2)) )),
% 0.21/0.50    inference(resolution,[],[f130,f76])).
% 0.21/0.50  % (11059)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 0.21/0.50    inference(global_subsumption,[],[f48,f46,f45,f44,f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f128,f78])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(resolution,[],[f70,f47])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sP1(X0,X2,X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.50    inference(definition_folding,[],[f27,f29,f28])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    ( ! [X0] : (sP0(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))) )),
% 0.21/0.50    inference(global_subsumption,[],[f179,f190,f254])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | sP0(sK2,X0,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) | ~sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))) )),
% 0.21/0.50    inference(superposition,[],[f251,f180])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK5(sK2,k2_struct_0(sK2),X0),k2_struct_0(sK2)) | sP0(sK2,X1,sK5(sK2,k2_struct_0(sK2),X0)) | ~sP0(sK2,k2_struct_0(sK2),X0)) )),
% 0.21/0.50    inference(global_subsumption,[],[f80,f250])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK5(sK2,k2_struct_0(sK2),X0),k2_struct_0(sK2)) | sP0(sK2,X1,sK5(sK2,k2_struct_0(sK2),X0)) | v1_xboole_0(k2_struct_0(sK2)) | ~sP0(sK2,k2_struct_0(sK2),X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f249,f78])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP0(sK2,X1,sK5(sK2,k2_struct_0(sK2),X0)) | v1_xboole_0(k2_struct_0(sK2)) | ~sP0(sK2,k2_struct_0(sK2),X0) | ~m1_subset_1(sK5(sK2,u1_struct_0(sK2),X0),u1_struct_0(sK2))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f248,f78])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(k2_struct_0(sK2)) | ~sP0(sK2,k2_struct_0(sK2),X0) | sP0(sK2,X1,sK5(sK2,u1_struct_0(sK2),X0)) | ~m1_subset_1(sK5(sK2,u1_struct_0(sK2),X0),u1_struct_0(sK2))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f247,f78])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP0(sK2,k2_struct_0(sK2),X0) | v1_xboole_0(u1_struct_0(sK2)) | sP0(sK2,X1,sK5(sK2,u1_struct_0(sK2),X0)) | ~m1_subset_1(sK5(sK2,u1_struct_0(sK2),X0),u1_struct_0(sK2))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f246,f78])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP0(sK2,u1_struct_0(sK2),X0) | v1_xboole_0(u1_struct_0(sK2)) | sP0(sK2,X1,sK5(sK2,u1_struct_0(sK2),X0)) | ~m1_subset_1(sK5(sK2,u1_struct_0(sK2),X0),u1_struct_0(sK2))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f242])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP0(sK2,u1_struct_0(sK2),X0) | v1_xboole_0(u1_struct_0(sK2)) | sP0(sK2,X1,sK5(sK2,u1_struct_0(sK2),X0)) | sP0(sK2,X1,sK5(sK2,u1_struct_0(sK2),X0)) | ~m1_subset_1(sK5(sK2,u1_struct_0(sK2),X0),u1_struct_0(sK2))) )),
% 0.21/0.50    inference(resolution,[],[f231,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    ( ! [X4,X2,X3] : (~m1_subset_1(sK4(sK2,X2,sK5(sK2,X3,X4)),X3) | ~sP0(sK2,X3,X4) | v1_xboole_0(X3) | sP0(sK2,X2,sK5(sK2,X3,X4))) )),
% 0.21/0.50    inference(resolution,[],[f228,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK4(sK2,X2,sK5(sK2,X0,X1)),X0) | sP0(sK2,X2,sK5(sK2,X0,X1)) | ~sP0(sK2,X0,X1)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f226])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~sP0(sK2,X0,X1) | sP0(sK2,X2,sK5(sK2,X0,X1)) | ~r2_hidden(sK4(sK2,X2,sK5(sK2,X0,X1)),X0) | ~sP0(sK2,X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f224,f83])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK5(sK2,X1,X2),k2_struct_0(sK2)) | ~sP0(sK2,X1,X2) | sP0(sK2,X0,sK5(sK2,X1,X2)) | ~r2_hidden(sK4(sK2,X0,sK5(sK2,X1,X2)),X1)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f222])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK4(sK2,X0,sK5(sK2,X1,X2)),X1) | ~sP0(sK2,X1,X2) | sP0(sK2,X0,sK5(sK2,X1,X2)) | ~m1_subset_1(sK5(sK2,X1,X2),k2_struct_0(sK2)) | sP0(sK2,X0,sK5(sK2,X1,X2)) | ~sP0(sK2,X1,X2)) )),
% 0.21/0.50    inference(resolution,[],[f122,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_orders_2(X0,sK4(X0,X1,sK5(X0,X2,X3)),sK5(X0,X2,X3)) | sP0(X0,X1,sK5(X0,X2,X3)) | ~sP0(X0,X2,X3)) )),
% 0.21/0.50    inference(resolution,[],[f72,f64])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_orders_2(X0,sK4(X0,X1,X3),X3) | sP0(X0,X1,X3)) )),
% 0.21/0.50    inference(equality_resolution,[],[f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | ~r2_orders_2(X0,sK4(X0,X1,X3),X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X4,X2,X5,X3] : (r2_orders_2(sK2,sK4(sK2,X2,X3),sK5(sK2,X4,X5)) | ~r2_hidden(sK4(sK2,X2,X3),X4) | ~sP0(sK2,X4,X5) | sP0(sK2,X2,X3) | ~m1_subset_1(X3,k2_struct_0(sK2))) )),
% 0.21/0.50    inference(resolution,[],[f120,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(sK4(sK2,X0,X1),k2_struct_0(sK2)) | sP0(sK2,X0,X1) | ~m1_subset_1(X1,k2_struct_0(sK2))) )),
% 0.21/0.50    inference(superposition,[],[f74,f78])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_struct_0(sK2))),
% 0.21/0.50    inference(global_subsumption,[],[f44,f77,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_struct_0(sK2)) | ~l1_struct_0(sK2) | v2_struct_0(sK2)),
% 0.21/0.50    inference(superposition,[],[f58,f78])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ~r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.50    inference(global_subsumption,[],[f179,f184])).
% 0.21/0.50  % (11051)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~r2_orders_2(sK2,sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2)))) | ~sP0(sK2,k2_struct_0(sK2),sK3(k1_orders_2(sK2,k2_struct_0(sK2)),k1_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.50    inference(superposition,[],[f84,f180])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_orders_2(sK2,sK5(sK2,X0,X1),sK5(sK2,X0,X1)) | ~sP0(sK2,X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f83,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_orders_2(sK2,X0,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f81,f78])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_orders_2(sK2,X0,X0)) )),
% 0.21/0.50    inference(resolution,[],[f75,f48])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X2,X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    k1_xboole_0 != k1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (11042)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (11050)------------------------------
% 0.21/0.50  % (11050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11048)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (11050)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (11050)Memory used [KB]: 6908
% 0.21/0.50  % (11050)Time elapsed: 0.086 s
% 0.21/0.50  % (11050)------------------------------
% 0.21/0.50  % (11050)------------------------------
% 0.21/0.50  % (11043)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (11037)Success in time 0.151 s
%------------------------------------------------------------------------------
