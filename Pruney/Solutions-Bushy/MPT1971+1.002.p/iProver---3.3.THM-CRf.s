%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1971+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:57 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  451 (9919 expanded)
%              Number of clauses        :  335 (2065 expanded)
%              Number of leaves         :   29 (2301 expanded)
%              Depth                    :   28
%              Number of atoms          : 2748 (172949 expanded)
%              Number of equality atoms :  398 (1108 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   52 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f60])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f48])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f64])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
     => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
          | ~ v2_waybel_7(sK5,k7_lattice3(X0))
          | ~ v13_waybel_0(sK5,k7_lattice3(X0))
          | ~ v2_waybel_0(sK5,k7_lattice3(X0))
          | v1_xboole_0(sK5)
          | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_waybel_7(sK5,X0)
          | ~ v12_waybel_0(sK5,X0)
          | ~ v1_waybel_0(sK5,X0)
          | v1_xboole_0(sK5) )
        & ( ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(sK5,k7_lattice3(X0))
            & v13_waybel_0(sK5,k7_lattice3(X0))
            & v2_waybel_0(sK5,k7_lattice3(X0))
            & ~ v1_xboole_0(sK5) )
          | ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(sK5,X0)
            & v12_waybel_0(sK5,X0)
            & v1_waybel_0(sK5,X0)
            & ~ v1_xboole_0(sK5) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              | ~ v2_waybel_7(X1,k7_lattice3(X0))
              | ~ v13_waybel_0(X1,k7_lattice3(X0))
              | ~ v2_waybel_0(X1,k7_lattice3(X0))
              | v1_xboole_0(X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_waybel_7(X1,X0)
              | ~ v12_waybel_0(X1,X0)
              | ~ v1_waybel_0(X1,X0)
              | v1_xboole_0(X1) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
                & v2_waybel_7(X1,k7_lattice3(X0))
                & v13_waybel_0(X1,k7_lattice3(X0))
                & v2_waybel_0(X1,k7_lattice3(X0))
                & ~ v1_xboole_0(X1) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X1,X0)
                & v12_waybel_0(X1,X0)
                & v1_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) ) ) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
            | ~ v2_waybel_7(X1,k7_lattice3(sK4))
            | ~ v13_waybel_0(X1,k7_lattice3(sK4))
            | ~ v2_waybel_0(X1,k7_lattice3(sK4))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
            | ~ v1_waybel_7(X1,sK4)
            | ~ v12_waybel_0(X1,sK4)
            | ~ v1_waybel_0(X1,sK4)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
              & v2_waybel_7(X1,k7_lattice3(sK4))
              & v13_waybel_0(X1,k7_lattice3(sK4))
              & v2_waybel_0(X1,k7_lattice3(sK4))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
              & v1_waybel_7(X1,sK4)
              & v12_waybel_0(X1,sK4)
              & v1_waybel_0(X1,sK4)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
      | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
      | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
      | ~ v2_waybel_0(sK5,k7_lattice3(sK4))
      | v1_xboole_0(sK5)
      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v1_waybel_7(sK5,sK4)
      | ~ v12_waybel_0(sK5,sK4)
      | ~ v1_waybel_0(sK5,sK4)
      | v1_xboole_0(sK5) )
    & ( ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
        & v2_waybel_7(sK5,k7_lattice3(sK4))
        & v13_waybel_0(sK5,k7_lattice3(sK4))
        & v2_waybel_0(sK5,k7_lattice3(sK4))
        & ~ v1_xboole_0(sK5) )
      | ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
        & v1_waybel_7(sK5,sK4)
        & v12_waybel_0(sK5,sK4)
        & v1_waybel_0(sK5,sK4)
        & ~ v1_xboole_0(sK5) ) )
    & l1_orders_2(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f65,f67,f66])).

fof(f112,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f105,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f115,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f68])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v13_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v13_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f62])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f128,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | v12_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f130,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f68])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f118,plain,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | v12_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f120,plain,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f68])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f55])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X2,X1)
          & r2_hidden(k13_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & ~ r2_hidden(X2,X1)
        & r2_hidden(k13_lattice3(X0,X2,sK3(X0,X1)),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k13_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK2(X0,X1),X1)
            & r2_hidden(k13_lattice3(X0,sK2(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & ~ r2_hidden(sK2(X0,X1),X1)
                & r2_hidden(k13_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f56,f58,f57])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f126,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f106,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => v1_lattice3(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f40,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(flattening,[],[f40])).

fof(f89,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f100,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f101,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f102,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f29,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f83,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v3_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f86,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => v4_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f36,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f87,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => v5_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f38,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
             => k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v2_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f50])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X2,X1)
          & r2_hidden(k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & ~ r2_hidden(X2,X1)
        & r2_hidden(k12_lattice3(X0,X2,sK1(X0,X1)),X1)
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK0(X0,X1),X1)
            & r2_hidden(k12_lattice3(X0,sK0(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK1(X0,X1),X1)
                & ~ r2_hidden(sK0(X0,X1),X1)
                & r2_hidden(k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f119,plain,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f129,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f114,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f131,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v1_xboole_0(sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ v1_waybel_0(sK5,sK4)
    | v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f68])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | r2_hidden(k12_lattice3(X0,sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f75,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k8_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k12_lattice3(X0,X1,X2) = k13_lattice3(k7_lattice3(X0),k8_lattice3(X0,X1),k8_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,X1,X2) = k13_lattice3(k7_lattice3(X0),k8_lattice3(X0,X1),k8_lattice3(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,X1,X2) = k13_lattice3(k7_lattice3(X0),k8_lattice3(X0,X1),k8_lattice3(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k13_lattice3(k7_lattice3(X0),k8_lattice3(X0,X1),k8_lattice3(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f127,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | v1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
         => k9_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k9_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | r2_hidden(k13_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f124,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,plain,
    ( v2_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_50,negated_conjecture,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_3691,plain,
    ( v2_waybel_0(X0,k7_lattice3(X1))
    | v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_50])).

cnf(c_3692,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3691])).

cnf(c_57,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_47,negated_conjecture,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3694,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3692,c_57,c_47])).

cnf(c_29,plain,
    ( ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_34,negated_conjecture,
    ( v12_waybel_0(sK5,sK4)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_2851,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_2852,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2851])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_2854,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2852,c_57,c_32])).

cnf(c_30,plain,
    ( v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_44,negated_conjecture,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | v12_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2804,plain,
    ( v13_waybel_0(X0,k7_lattice3(X1))
    | v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_44])).

cnf(c_2805,plain,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2804])).

cnf(c_42,negated_conjecture,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2807,plain,
    ( v13_waybel_0(sK5,k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2805,c_57,c_42])).

cnf(c_10,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_56,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_369,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36,c_56])).

cnf(c_1150,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_369])).

cnf(c_1151,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | m1_subset_1(sK2(X0,sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1150])).

cnf(c_20,plain,
    ( v1_lattice3(k7_lattice3(X0))
    | ~ v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_58,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_907,plain,
    ( v1_lattice3(k7_lattice3(X0))
    | ~ l1_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_58])).

cnf(c_908,plain,
    ( v1_lattice3(k7_lattice3(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_907])).

cnf(c_910,plain,
    ( v1_lattice3(k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_908,c_57])).

cnf(c_1704,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | m1_subset_1(sK2(X0,sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1151,c_910])).

cnf(c_1705,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1704])).

cnf(c_2919,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2807,c_1705])).

cnf(c_2934,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2854,c_2919])).

cnf(c_3745,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3694,c_2934])).

cnf(c_7366,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(subtyping,[status(esa)],[c_3745])).

cnf(c_8430,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7366])).

cnf(c_62,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_63,plain,
    ( v3_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_61,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_64,plain,
    ( v4_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_60,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_65,plain,
    ( v5_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_68,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_2856,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2854])).

cnf(c_2920,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) != iProver_top
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2919])).

cnf(c_3696,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3694])).

cnf(c_14,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(k7_lattice3(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_7395,plain,
    ( ~ l1_orders_2(X0_57)
    | l1_orders_2(k7_lattice3(X0_57)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_7458,plain,
    ( l1_orders_2(X0_57) != iProver_top
    | l1_orders_2(k7_lattice3(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7395])).

cnf(c_7460,plain,
    ( l1_orders_2(k7_lattice3(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7458])).

cnf(c_17,plain,
    ( ~ v3_orders_2(X0)
    | v3_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7392,plain,
    ( ~ v3_orders_2(X0_57)
    | v3_orders_2(k7_lattice3(X0_57))
    | ~ l1_orders_2(X0_57) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_7467,plain,
    ( v3_orders_2(X0_57) != iProver_top
    | v3_orders_2(k7_lattice3(X0_57)) = iProver_top
    | l1_orders_2(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7392])).

cnf(c_7469,plain,
    ( v3_orders_2(k7_lattice3(sK4)) = iProver_top
    | v3_orders_2(sK4) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7467])).

cnf(c_18,plain,
    ( ~ v4_orders_2(X0)
    | v4_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_7391,plain,
    ( ~ v4_orders_2(X0_57)
    | v4_orders_2(k7_lattice3(X0_57))
    | ~ l1_orders_2(X0_57) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_7470,plain,
    ( v4_orders_2(X0_57) != iProver_top
    | v4_orders_2(k7_lattice3(X0_57)) = iProver_top
    | l1_orders_2(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7391])).

cnf(c_7472,plain,
    ( v4_orders_2(k7_lattice3(sK4)) = iProver_top
    | v4_orders_2(sK4) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7470])).

cnf(c_19,plain,
    ( ~ v5_orders_2(X0)
    | v5_orders_2(k7_lattice3(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_7390,plain,
    ( ~ v5_orders_2(X0_57)
    | v5_orders_2(k7_lattice3(X0_57))
    | ~ l1_orders_2(X0_57) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_7473,plain,
    ( v5_orders_2(X0_57) != iProver_top
    | v5_orders_2(k7_lattice3(X0_57)) = iProver_top
    | l1_orders_2(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7390])).

cnf(c_7475,plain,
    ( v5_orders_2(k7_lattice3(sK4)) = iProver_top
    | v5_orders_2(sK4) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7473])).

cnf(c_9499,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8430,c_63,c_64,c_65,c_68,c_2856,c_2920,c_3696,c_7460,c_7469,c_7472,c_7475])).

cnf(c_9,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1186,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK3(X1,X0),u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_369])).

cnf(c_1187,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | m1_subset_1(sK3(X0,sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1186])).

cnf(c_1673,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | m1_subset_1(sK3(X0,sK5),u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1187,c_910])).

cnf(c_1674,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1673])).

cnf(c_2918,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2807,c_1674])).

cnf(c_2935,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2854,c_2918])).

cnf(c_3744,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3694,c_2935])).

cnf(c_7367,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(subtyping,[status(esa)],[c_3744])).

cnf(c_8429,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7367])).

cnf(c_2921,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) != iProver_top
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2918])).

cnf(c_9441,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8429,c_63,c_64,c_65,c_68,c_2856,c_2921,c_3696,c_7460,c_7469,c_7472,c_7475])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,k9_lattice3(X1,X0),k9_lattice3(X1,X2)) = k13_lattice3(k7_lattice3(X1),X0,X2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k12_lattice3(X1,k9_lattice3(X1,X0),k9_lattice3(X1,X2)) = k13_lattice3(k7_lattice3(X1),X0,X2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_58])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | k12_lattice3(sK4,k9_lattice3(sK4,X1),k9_lattice3(sK4,X0)) = k13_lattice3(k7_lattice3(sK4),X1,X0) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_678,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | k12_lattice3(sK4,k9_lattice3(sK4,X1),k9_lattice3(sK4,X0)) = k13_lattice3(k7_lattice3(sK4),X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_62,c_61,c_60,c_57])).

cnf(c_7383,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1_56,u1_struct_0(k7_lattice3(sK4)))
    | k12_lattice3(sK4,k9_lattice3(sK4,X1_56),k9_lattice3(sK4,X0_56)) = k13_lattice3(k7_lattice3(sK4),X1_56,X0_56) ),
    inference(subtyping,[status(esa)],[c_678])).

cnf(c_8411,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,X0_56),k9_lattice3(sK4,X1_56)) = k13_lattice3(k7_lattice3(sK4),X0_56,X1_56)
    | m1_subset_1(X0_56,u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(k7_lattice3(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7383])).

cnf(c_9447,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,X0_56),k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))) = k13_lattice3(k7_lattice3(sK4),X0_56,sK3(k7_lattice3(sK4),sK5))
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(X0_56,u1_struct_0(k7_lattice3(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9441,c_8411])).

cnf(c_9503,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))) = k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5))
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9499,c_9447])).

cnf(c_24,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | v1_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_28,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_4,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_757,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_58])).

cnf(c_758,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_757])).

cnf(c_762,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_758,c_62,c_61,c_60,c_57])).

cnf(c_1050,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_762,c_369])).

cnf(c_1051,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_1050])).

cnf(c_2661,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_1051])).

cnf(c_2662,plain,
    ( ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2661])).

cnf(c_43,negated_conjecture,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_2664,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2662,c_57,c_43,c_33])).

cnf(c_2665,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2664])).

cnf(c_3641,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_2665])).

cnf(c_3642,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3641])).

cnf(c_48,negated_conjecture,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3644,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3642,c_57,c_48,c_32,c_2852])).

cnf(c_3645,plain,
    ( m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3644])).

cnf(c_31,negated_conjecture,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_378,plain,
    ( ~ v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v12_waybel_0(sK5,sK4)
    | ~ v1_waybel_0(sK5,sK4)
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_0(sK5,k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_56])).

cnf(c_379,negated_conjecture,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_378])).

cnf(c_2761,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_379])).

cnf(c_2762,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2761])).

cnf(c_2764,plain,
    ( ~ v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_0(sK5,k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2762,c_57])).

cnf(c_2765,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2764])).

cnf(c_2815,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2807,c_2765])).

cnf(c_2862,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2854,c_2815])).

cnf(c_3553,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_2862])).

cnf(c_3554,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3553])).

cnf(c_3556,plain,
    ( ~ v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3554,c_57,c_32,c_2852])).

cnf(c_3557,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3556])).

cnf(c_3701,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3694,c_3557])).

cnf(c_3922,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_3645,c_3701])).

cnf(c_3923,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3922])).

cnf(c_3,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_787,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_58])).

cnf(c_788,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_792,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_788,c_62,c_61,c_60,c_57])).

cnf(c_1031,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,X0),u1_struct_0(sK4))
    | v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_792,c_369])).

cnf(c_1032,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_1031])).

cnf(c_2681,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_1032])).

cnf(c_2682,plain,
    ( ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2681])).

cnf(c_2684,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2682,c_57,c_43,c_33])).

cnf(c_2685,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2684])).

cnf(c_3624,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_2685])).

cnf(c_3625,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3624])).

cnf(c_3627,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3625,c_57,c_48,c_32,c_2852])).

cnf(c_3628,plain,
    ( m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3627])).

cnf(c_3960,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(resolution,[status(thm)],[c_3628,c_3701])).

cnf(c_3961,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3960])).

cnf(c_2,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k12_lattice3(X1,sK0(X1,X0),sK1(X1,X0)),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_817,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k12_lattice3(X1,sK0(X1,X0),sK1(X1,X0)),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_58])).

cnf(c_818,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,X0),sK1(sK4,X0)),X0)
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_817])).

cnf(c_822,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,X0),sK1(sK4,X0)),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_818,c_62,c_61,c_60,c_57])).

cnf(c_1012,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,X0),sK1(sK4,X0)),X0)
    | v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_822,c_369])).

cnf(c_1013,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_1012])).

cnf(c_2701,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_1013])).

cnf(c_2702,plain,
    ( ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2701])).

cnf(c_2704,plain,
    ( v1_waybel_7(sK5,sK4)
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2702,c_57,c_43,c_33])).

cnf(c_2705,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2704])).

cnf(c_3607,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_2705])).

cnf(c_3608,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3607])).

cnf(c_3610,plain,
    ( v1_waybel_7(sK5,sK4)
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3608,c_57,c_48,c_32,c_2852])).

cnf(c_3611,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3610])).

cnf(c_3998,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5) ),
    inference(resolution,[status(thm)],[c_3611,c_3701])).

cnf(c_3999,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3998])).

cnf(c_1,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_847,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_58])).

cnf(c_848,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_852,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_848,c_62,c_61,c_60,c_57])).

cnf(c_993,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_852,c_369])).

cnf(c_994,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_993])).

cnf(c_2721,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_994])).

cnf(c_2722,plain,
    ( ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2721])).

cnf(c_2724,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2722,c_57,c_43,c_33])).

cnf(c_2725,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2724])).

cnf(c_3590,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_2725])).

cnf(c_3591,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3590])).

cnf(c_3593,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3591,c_57,c_48,c_32,c_2852])).

cnf(c_3594,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3593])).

cnf(c_4036,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK4,sK5),sK5) ),
    inference(resolution,[status(thm)],[c_3594,c_3701])).

cnf(c_4037,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK0(sK4,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4036])).

cnf(c_0,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_877,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK1(X1,X0),X0)
    | v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_58])).

cnf(c_878,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_877])).

cnf(c_882,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_878,c_62,c_61,c_60,c_57])).

cnf(c_974,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,X0),X0)
    | v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_882,c_369])).

cnf(c_975,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_974])).

cnf(c_2741,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_975])).

cnf(c_2742,plain,
    ( ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2741])).

cnf(c_2744,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2742,c_57,c_43,c_33])).

cnf(c_2745,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2744])).

cnf(c_3573,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_2745])).

cnf(c_3574,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3573])).

cnf(c_3576,plain,
    ( v1_waybel_7(sK5,sK4)
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3574,c_57,c_48,c_32,c_2852])).

cnf(c_3577,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5)
    | v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3576])).

cnf(c_4074,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK4,sK5),sK5) ),
    inference(resolution,[status(thm)],[c_3577,c_3701])).

cnf(c_4075,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(sK4,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4074])).

cnf(c_7411,plain,
    ( X0_57 != X1_57
    | X0_56 != X1_56
    | sK1(X0_57,X0_56) = sK1(X1_57,X1_56) ),
    theory(equality)).

cnf(c_7430,plain,
    ( sK4 != sK4
    | sK1(sK4,sK5) = sK1(sK4,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_7411])).

cnf(c_7420,plain,
    ( X0_57 != X1_57
    | X0_56 != X1_56
    | sK0(X0_57,X0_56) = sK0(X1_57,X1_56) ),
    theory(equality)).

cnf(c_7439,plain,
    ( sK4 != sK4
    | sK0(sK4,sK5) = sK0(sK4,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_7420])).

cnf(c_7428,plain,
    ( X0_57 != X1_57
    | k7_lattice3(X0_57) = k7_lattice3(X1_57) ),
    theory(equality)).

cnf(c_7447,plain,
    ( k7_lattice3(sK4) = k7_lattice3(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_7428])).

cnf(c_7405,plain,
    ( X0_56 = X0_56 ),
    theory(equality)).

cnf(c_7449,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_7405])).

cnf(c_7406,plain,
    ( X0_57 = X0_57 ),
    theory(equality)).

cnf(c_7450,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_7406])).

cnf(c_27,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2950,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ l1_orders_2(X1)
    | k7_lattice3(X1) != k7_lattice3(sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_2807])).

cnf(c_2951,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
    | ~ l1_orders_2(X0)
    | k7_lattice3(X0) != k7_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_2950])).

cnf(c_7379,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_57)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_57))))
    | ~ l1_orders_2(X0_57)
    | k7_lattice3(X0_57) != k7_lattice3(sK4) ),
    inference(subtyping,[status(esa)],[c_2951])).

cnf(c_7490,plain,
    ( k7_lattice3(X0_57) != k7_lattice3(sK4)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0_57))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0_57)))) != iProver_top
    | l1_orders_2(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7379])).

cnf(c_7492,plain,
    ( k7_lattice3(sK4) != k7_lattice3(sK4)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7490])).

cnf(c_11,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(X1,X3,X2),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1102,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k13_lattice3(X1,X3,X2),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_369])).

cnf(c_1103,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | ~ v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X1,sK5)
    | r2_hidden(X2,sK5)
    | ~ r2_hidden(k13_lattice3(X0,X2,X1),sK5)
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1102])).

cnf(c_1735,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | ~ v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(X2,sK5)
    | r2_hidden(X1,sK5)
    | ~ r2_hidden(k13_lattice3(X0,X2,X1),sK5)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1103,c_910])).

cnf(c_1736,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X0,X1),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1735])).

cnf(c_2915,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X0,X1),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2807,c_1736])).

cnf(c_2931,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X0,X1),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2854,c_2915])).

cnf(c_3741,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK4)))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X0,X1),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3694,c_2931])).

cnf(c_7370,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0_56,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1_56,u1_struct_0(k7_lattice3(sK4)))
    | r2_hidden(X1_56,sK5)
    | r2_hidden(X0_56,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X0_56,X1_56),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(subtyping,[status(esa)],[c_3741])).

cnf(c_7401,plain,
    ( ~ v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4))
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_7370])).

cnf(c_7504,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) != iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7401])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k8_lattice3(X1,X0),u1_struct_0(k7_lattice3(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_7394,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(X0_57))
    | m1_subset_1(k8_lattice3(X0_57,X0_56),u1_struct_0(k7_lattice3(X0_57)))
    | ~ l1_orders_2(X0_57) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_8896,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK4))
    | m1_subset_1(k8_lattice3(sK4,X0_56),u1_struct_0(k7_lattice3(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_7394])).

cnf(c_9295,plain,
    ( m1_subset_1(k8_lattice3(sK4,sK1(sK4,sK5)),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_8896])).

cnf(c_9321,plain,
    ( m1_subset_1(k8_lattice3(sK4,sK1(sK4,sK5)),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9295])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | k8_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_7397,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(X0_57))
    | ~ l1_orders_2(X0_57)
    | k8_lattice3(X0_57,X0_56) = X0_56 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_9324,plain,
    ( ~ m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_7397])).

cnf(c_9325,plain,
    ( k8_lattice3(sK4,sK1(sK4,sK5)) = sK1(sK4,sK5)
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9324])).

cnf(c_9342,plain,
    ( m1_subset_1(k8_lattice3(sK4,sK0(sK4,sK5)),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_8896])).

cnf(c_9368,plain,
    ( m1_subset_1(k8_lattice3(sK4,sK0(sK4,sK5)),u1_struct_0(k7_lattice3(sK4))) = iProver_top
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9342])).

cnf(c_9371,plain,
    ( ~ m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | k8_lattice3(sK4,sK0(sK4,sK5)) = sK0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_7397])).

cnf(c_9372,plain,
    ( k8_lattice3(sK4,sK0(sK4,sK5)) = sK0(sK4,sK5)
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9371])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(k7_lattice3(X1),k8_lattice3(X1,X0),k8_lattice3(X1,X2)) = k12_lattice3(X1,X0,X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_694,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k13_lattice3(k7_lattice3(X1),k8_lattice3(X1,X2),k8_lattice3(X1,X0)) = k12_lattice3(X1,X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_58])).

cnf(c_695,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,X0),k8_lattice3(sK4,X1)) = k12_lattice3(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_699,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,X0),k8_lattice3(sK4,X1)) = k12_lattice3(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_62,c_61,c_60,c_57])).

cnf(c_7382,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK4))
    | k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,X0_56),k8_lattice3(sK4,X1_56)) = k12_lattice3(sK4,X0_56,X1_56) ),
    inference(subtyping,[status(esa)],[c_699])).

cnf(c_9347,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK4))
    | ~ m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),k8_lattice3(sK4,X0_56)) = k12_lattice3(sK4,sK0(sK4,sK5),X0_56) ),
    inference(instantiation,[status(thm)],[c_7382])).

cnf(c_9649,plain,
    ( ~ m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4))
    | ~ m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4))
    | k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),k8_lattice3(sK4,sK1(sK4,sK5))) = k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_9347])).

cnf(c_9650,plain,
    ( k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),k8_lattice3(sK4,sK1(sK4,sK5))) = k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5))
    | m1_subset_1(sK0(sK4,sK5),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK1(sK4,sK5),u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9649])).

cnf(c_7408,plain,
    ( X0_56 != X1_56
    | X2_56 != X1_56
    | X2_56 = X0_56 ),
    theory(equality)).

cnf(c_8863,plain,
    ( X0_56 != X1_56
    | X0_56 = k8_lattice3(X0_57,X2_56)
    | k8_lattice3(X0_57,X2_56) != X1_56 ),
    inference(instantiation,[status(thm)],[c_7408])).

cnf(c_9748,plain,
    ( X0_56 = k8_lattice3(sK4,sK1(sK4,sK5))
    | X0_56 != sK1(sK4,sK5)
    | k8_lattice3(sK4,sK1(sK4,sK5)) != sK1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_8863])).

cnf(c_10746,plain,
    ( k8_lattice3(sK4,sK1(sK4,sK5)) != sK1(sK4,sK5)
    | sK1(sK4,sK5) = k8_lattice3(sK4,sK1(sK4,sK5))
    | sK1(sK4,sK5) != sK1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_9748])).

cnf(c_9790,plain,
    ( X0_56 = k8_lattice3(sK4,sK0(sK4,sK5))
    | X0_56 != sK0(sK4,sK5)
    | k8_lattice3(sK4,sK0(sK4,sK5)) != sK0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_8863])).

cnf(c_10760,plain,
    ( k8_lattice3(sK4,sK0(sK4,sK5)) != sK0(sK4,sK5)
    | sK0(sK4,sK5) = k8_lattice3(sK4,sK0(sK4,sK5))
    | sK0(sK4,sK5) != sK0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_9790])).

cnf(c_7412,plain,
    ( ~ r2_hidden(X0_56,X1_56)
    | r2_hidden(X2_56,X3_56)
    | X2_56 != X0_56
    | X3_56 != X1_56 ),
    theory(equality)).

cnf(c_10299,plain,
    ( r2_hidden(X0_56,X1_56)
    | ~ r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | X0_56 != k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5))
    | X1_56 != sK5 ),
    inference(instantiation,[status(thm)],[c_7412])).

cnf(c_11763,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),k8_lattice3(sK4,sK1(sK4,sK5))),X0_56)
    | ~ r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5)
    | X0_56 != sK5
    | k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),k8_lattice3(sK4,sK1(sK4,sK5))) != k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_10299])).

cnf(c_11764,plain,
    ( X0_56 != sK5
    | k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),k8_lattice3(sK4,sK1(sK4,sK5))) != k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5))
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),k8_lattice3(sK4,sK1(sK4,sK5))),X0_56) = iProver_top
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11763])).

cnf(c_11766,plain,
    ( k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),k8_lattice3(sK4,sK1(sK4,sK5))) != k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5))
    | sK5 != sK5
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),k8_lattice3(sK4,sK1(sK4,sK5))),sK5) = iProver_top
    | r2_hidden(k12_lattice3(sK4,sK0(sK4,sK5),sK1(sK4,sK5)),sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11764])).

cnf(c_7400,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(X1_56,u1_struct_0(k7_lattice3(sK4)))
    | r2_hidden(X1_56,sK5)
    | r2_hidden(X0_56,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),X0_56,X1_56),sK5)
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_7370])).

cnf(c_9754,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(k8_lattice3(sK4,sK0(sK4,sK5)),u1_struct_0(k7_lattice3(sK4)))
    | r2_hidden(X0_56,sK5)
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),X0_56),sK5)
    | r2_hidden(k8_lattice3(sK4,sK0(sK4,sK5)),sK5)
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_7400])).

cnf(c_11789,plain,
    ( ~ m1_subset_1(k8_lattice3(sK4,sK0(sK4,sK5)),u1_struct_0(k7_lattice3(sK4)))
    | ~ m1_subset_1(k8_lattice3(sK4,sK1(sK4,sK5)),u1_struct_0(k7_lattice3(sK4)))
    | ~ r2_hidden(k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),k8_lattice3(sK4,sK1(sK4,sK5))),sK5)
    | r2_hidden(k8_lattice3(sK4,sK0(sK4,sK5)),sK5)
    | r2_hidden(k8_lattice3(sK4,sK1(sK4,sK5)),sK5)
    | ~ sP1_iProver_split ),
    inference(instantiation,[status(thm)],[c_9754])).

cnf(c_11790,plain,
    ( m1_subset_1(k8_lattice3(sK4,sK0(sK4,sK5)),u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | m1_subset_1(k8_lattice3(sK4,sK1(sK4,sK5)),u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),k8_lattice3(sK4,sK0(sK4,sK5)),k8_lattice3(sK4,sK1(sK4,sK5))),sK5) != iProver_top
    | r2_hidden(k8_lattice3(sK4,sK0(sK4,sK5)),sK5) = iProver_top
    | r2_hidden(k8_lattice3(sK4,sK1(sK4,sK5)),sK5) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11789])).

cnf(c_9285,plain,
    ( ~ r2_hidden(X0_56,X1_56)
    | r2_hidden(sK1(sK4,sK5),sK5)
    | sK1(sK4,sK5) != X0_56
    | sK5 != X1_56 ),
    inference(instantiation,[status(thm)],[c_7412])).

cnf(c_12595,plain,
    ( ~ r2_hidden(k8_lattice3(sK4,sK1(sK4,sK5)),X0_56)
    | r2_hidden(sK1(sK4,sK5),sK5)
    | sK1(sK4,sK5) != k8_lattice3(sK4,sK1(sK4,sK5))
    | sK5 != X0_56 ),
    inference(instantiation,[status(thm)],[c_9285])).

cnf(c_12596,plain,
    ( sK1(sK4,sK5) != k8_lattice3(sK4,sK1(sK4,sK5))
    | sK5 != X0_56
    | r2_hidden(k8_lattice3(sK4,sK1(sK4,sK5)),X0_56) != iProver_top
    | r2_hidden(sK1(sK4,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12595])).

cnf(c_12598,plain,
    ( sK1(sK4,sK5) != k8_lattice3(sK4,sK1(sK4,sK5))
    | sK5 != sK5
    | r2_hidden(k8_lattice3(sK4,sK1(sK4,sK5)),sK5) != iProver_top
    | r2_hidden(sK1(sK4,sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12596])).

cnf(c_9290,plain,
    ( ~ r2_hidden(X0_56,X1_56)
    | r2_hidden(sK0(sK4,sK5),sK5)
    | sK0(sK4,sK5) != X0_56
    | sK5 != X1_56 ),
    inference(instantiation,[status(thm)],[c_7412])).

cnf(c_12612,plain,
    ( ~ r2_hidden(k8_lattice3(sK4,sK0(sK4,sK5)),X0_56)
    | r2_hidden(sK0(sK4,sK5),sK5)
    | sK0(sK4,sK5) != k8_lattice3(sK4,sK0(sK4,sK5))
    | sK5 != X0_56 ),
    inference(instantiation,[status(thm)],[c_9290])).

cnf(c_12613,plain,
    ( sK0(sK4,sK5) != k8_lattice3(sK4,sK0(sK4,sK5))
    | sK5 != X0_56
    | r2_hidden(k8_lattice3(sK4,sK0(sK4,sK5)),X0_56) != iProver_top
    | r2_hidden(sK0(sK4,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12612])).

cnf(c_12615,plain,
    ( sK0(sK4,sK5) != k8_lattice3(sK4,sK0(sK4,sK5))
    | sK5 != sK5
    | r2_hidden(k8_lattice3(sK4,sK0(sK4,sK5)),sK5) != iProver_top
    | r2_hidden(sK0(sK4,sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12613])).

cnf(c_12841,plain,
    ( k12_lattice3(sK4,k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))) = k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9503,c_63,c_64,c_65,c_68,c_2856,c_3923,c_3961,c_3999,c_4037,c_4075,c_7430,c_7439,c_7447,c_7449,c_7450,c_7460,c_7469,c_7472,c_7475,c_7492,c_7504,c_9321,c_9325,c_9368,c_9372,c_9650,c_10746,c_10760,c_11766,c_11790,c_12598,c_12615])).

cnf(c_5,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(X1,X3,X2),X0)
    | ~ v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_715,plain,
    ( ~ v1_waybel_0(X0,X1)
    | ~ v12_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | r2_hidden(X3,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(X1,X3,X2),X0)
    | ~ v1_waybel_7(X0,X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_58])).

cnf(c_716,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X2,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X2,X1),X0)
    | ~ v1_waybel_7(X0,sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ l1_orders_2(sK4)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_720,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X2,X0)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X2,X1),X0)
    | ~ v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_62,c_61,c_60,c_57])).

cnf(c_721,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X1,X2),X0)
    | ~ v1_waybel_7(X0,sK4)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_720])).

cnf(c_1069,plain,
    ( ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | r2_hidden(X1,X0)
    | r2_hidden(X2,X0)
    | ~ r2_hidden(k12_lattice3(sK4,X2,X1),X0)
    | ~ v1_waybel_7(X0,sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_721,c_369])).

cnf(c_1070,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5)
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(unflattening,[status(thm)],[c_1069])).

cnf(c_2625,plain,
    ( ~ v13_waybel_0(X0,k7_lattice3(X1))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X2,sK5)
    | r2_hidden(X3,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X2,X3),sK5)
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_1070])).

cnf(c_2626,plain,
    ( ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5)
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_2625])).

cnf(c_2256,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ v12_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5) ),
    inference(resolution,[status(thm)],[c_33,c_1070])).

cnf(c_35,negated_conjecture,
    ( v1_waybel_0(sK5,sK4)
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2260,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2256,c_35,c_34,c_32])).

cnf(c_2261,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5) ),
    inference(renaming,[status(thm)],[c_2260])).

cnf(c_2454,plain,
    ( v13_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5)
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(resolution,[status(thm)],[c_44,c_1070])).

cnf(c_2630,plain,
    ( ~ v1_waybel_7(sK5,sK4)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5)
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2626,c_57,c_2261,c_2454])).

cnf(c_2631,plain,
    ( ~ v1_waybel_0(sK5,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5)
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_2630])).

cnf(c_3658,plain,
    ( ~ v2_waybel_0(X0,k7_lattice3(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k7_lattice3(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(sK4))
    | ~ m1_subset_1(X3,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X2,sK5)
    | r2_hidden(X3,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X2,X3),sK5)
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(X1)
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_2631])).

cnf(c_3659,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X0,sK5)
    | r2_hidden(X1,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5)
    | ~ v1_waybel_7(sK5,sK4)
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_3658])).

cnf(c_3508,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5)
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(resolution,[status(thm)],[c_50,c_2631])).

cnf(c_3663,plain,
    ( ~ v1_waybel_7(sK5,sK4)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5)
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3659,c_57,c_32,c_2852,c_3508])).

cnf(c_3664,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ m1_subset_1(X1,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1,sK5)
    | r2_hidden(X0,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0,X1),sK5)
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_3663])).

cnf(c_7373,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(X1_56,sK5)
    | r2_hidden(X0_56,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0_56,X1_56),sK5)
    | ~ v1_waybel_7(sK5,sK4) ),
    inference(subtyping,[status(esa)],[c_3664])).

cnf(c_7398,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(sK4))
    | ~ m1_subset_1(X1_56,u1_struct_0(sK4))
    | r2_hidden(X1_56,sK5)
    | r2_hidden(X0_56,sK5)
    | ~ r2_hidden(k12_lattice3(sK4,X0_56,X1_56),sK5)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_7373])).

cnf(c_8422,plain,
    ( m1_subset_1(X0_56,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1_56,u1_struct_0(sK4)) != iProver_top
    | r2_hidden(X0_56,sK5) = iProver_top
    | r2_hidden(X1_56,sK5) = iProver_top
    | r2_hidden(k12_lattice3(sK4,X0_56,X1_56),sK5) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7398])).

cnf(c_12843,plain,
    ( m1_subset_1(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)),u1_struct_0(sK4)) != iProver_top
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5)),sK5) != iProver_top
    | r2_hidden(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),sK5) = iProver_top
    | r2_hidden(k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)),sK5) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_12841,c_8422])).

cnf(c_8548,plain,
    ( ~ r2_hidden(X0_56,X1_56)
    | r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5)
    | sK2(k7_lattice3(sK4),sK5) != X0_56
    | sK5 != X1_56 ),
    inference(instantiation,[status(thm)],[c_7412])).

cnf(c_12648,plain,
    ( ~ r2_hidden(k9_lattice3(X0_57,sK2(k7_lattice3(sK4),sK5)),X0_56)
    | r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5)
    | sK2(k7_lattice3(sK4),sK5) != k9_lattice3(X0_57,sK2(k7_lattice3(sK4),sK5))
    | sK5 != X0_56 ),
    inference(instantiation,[status(thm)],[c_8548])).

cnf(c_12649,plain,
    ( sK2(k7_lattice3(sK4),sK5) != k9_lattice3(X0_57,sK2(k7_lattice3(sK4),sK5))
    | sK5 != X0_56
    | r2_hidden(k9_lattice3(X0_57,sK2(k7_lattice3(sK4),sK5)),X0_56) != iProver_top
    | r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12648])).

cnf(c_12651,plain,
    ( sK2(k7_lattice3(sK4),sK5) != k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5))
    | sK5 != sK5
    | r2_hidden(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),sK5) != iProver_top
    | r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12649])).

cnf(c_8541,plain,
    ( ~ r2_hidden(X0_56,X1_56)
    | r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5)
    | sK3(k7_lattice3(sK4),sK5) != X0_56
    | sK5 != X1_56 ),
    inference(instantiation,[status(thm)],[c_7412])).

cnf(c_12623,plain,
    ( ~ r2_hidden(k9_lattice3(X0_57,sK3(k7_lattice3(sK4),sK5)),X0_56)
    | r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5)
    | sK3(k7_lattice3(sK4),sK5) != k9_lattice3(X0_57,sK3(k7_lattice3(sK4),sK5))
    | sK5 != X0_56 ),
    inference(instantiation,[status(thm)],[c_8541])).

cnf(c_12624,plain,
    ( sK3(k7_lattice3(sK4),sK5) != k9_lattice3(X0_57,sK3(k7_lattice3(sK4),sK5))
    | sK5 != X0_56
    | r2_hidden(k9_lattice3(X0_57,sK3(k7_lattice3(sK4),sK5)),X0_56) != iProver_top
    | r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12623])).

cnf(c_12626,plain,
    ( sK3(k7_lattice3(sK4),sK5) != k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))
    | sK5 != sK5
    | r2_hidden(k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)),sK5) != iProver_top
    | r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_12624])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(X1)))
    | ~ l1_orders_2(X1)
    | k9_lattice3(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7396,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(k7_lattice3(X0_57)))
    | ~ l1_orders_2(X0_57)
    | k9_lattice3(X0_57,X0_56) = X0_56 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_8398,plain,
    ( k9_lattice3(X0_57,X0_56) = X0_56
    | m1_subset_1(X0_56,u1_struct_0(k7_lattice3(X0_57))) != iProver_top
    | l1_orders_2(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7396])).

cnf(c_9508,plain,
    ( k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)) = sK2(k7_lattice3(sK4),sK5)
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9499,c_8398])).

cnf(c_9449,plain,
    ( k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)) = sK3(k7_lattice3(sK4),sK5)
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9441,c_8398])).

cnf(c_8701,plain,
    ( X0_56 != X1_56
    | sK2(k7_lattice3(sK4),sK5) != X1_56
    | sK2(k7_lattice3(sK4),sK5) = X0_56 ),
    inference(instantiation,[status(thm)],[c_7408])).

cnf(c_8883,plain,
    ( X0_56 != sK2(k7_lattice3(sK4),sK5)
    | sK2(k7_lattice3(sK4),sK5) = X0_56
    | sK2(k7_lattice3(sK4),sK5) != sK2(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_8701])).

cnf(c_9096,plain,
    ( k9_lattice3(X0_57,sK2(k7_lattice3(sK4),sK5)) != sK2(k7_lattice3(sK4),sK5)
    | sK2(k7_lattice3(sK4),sK5) = k9_lattice3(X0_57,sK2(k7_lattice3(sK4),sK5))
    | sK2(k7_lattice3(sK4),sK5) != sK2(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_8883])).

cnf(c_9097,plain,
    ( k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)) != sK2(k7_lattice3(sK4),sK5)
    | sK2(k7_lattice3(sK4),sK5) = k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5))
    | sK2(k7_lattice3(sK4),sK5) != sK2(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_9096])).

cnf(c_8692,plain,
    ( X0_56 != X1_56
    | sK3(k7_lattice3(sK4),sK5) != X1_56
    | sK3(k7_lattice3(sK4),sK5) = X0_56 ),
    inference(instantiation,[status(thm)],[c_7408])).

cnf(c_8878,plain,
    ( X0_56 != sK3(k7_lattice3(sK4),sK5)
    | sK3(k7_lattice3(sK4),sK5) = X0_56
    | sK3(k7_lattice3(sK4),sK5) != sK3(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_8692])).

cnf(c_9089,plain,
    ( k9_lattice3(X0_57,sK3(k7_lattice3(sK4),sK5)) != sK3(k7_lattice3(sK4),sK5)
    | sK3(k7_lattice3(sK4),sK5) = k9_lattice3(X0_57,sK3(k7_lattice3(sK4),sK5))
    | sK3(k7_lattice3(sK4),sK5) != sK3(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_8878])).

cnf(c_9090,plain,
    ( k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)) != sK3(k7_lattice3(sK4),sK5)
    | sK3(k7_lattice3(sK4),sK5) = k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5))
    | sK3(k7_lattice3(sK4),sK5) != sK3(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_9089])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(X1)))
    | m1_subset_1(k9_lattice3(X1,X0),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_7393,plain,
    ( ~ m1_subset_1(X0_56,u1_struct_0(k7_lattice3(X0_57)))
    | m1_subset_1(k9_lattice3(X0_57,X0_56),u1_struct_0(X0_57))
    | ~ l1_orders_2(X0_57) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_8921,plain,
    ( m1_subset_1(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_7393])).

cnf(c_8922,plain,
    ( m1_subset_1(k9_lattice3(sK4,sK2(k7_lattice3(sK4),sK5)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK2(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8921])).

cnf(c_8918,plain,
    ( m1_subset_1(k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)),u1_struct_0(sK4))
    | ~ m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_7393])).

cnf(c_8919,plain,
    ( m1_subset_1(k9_lattice3(sK4,sK3(k7_lattice3(sK4),sK5)),u1_struct_0(sK4)) = iProver_top
    | m1_subset_1(sK3(k7_lattice3(sK4),sK5),u1_struct_0(k7_lattice3(sK4))) != iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8918])).

cnf(c_8871,plain,
    ( sK2(k7_lattice3(sK4),sK5) = sK2(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_7405])).

cnf(c_8868,plain,
    ( sK3(k7_lattice3(sK4),sK5) = sK3(k7_lattice3(sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_7405])).

cnf(c_7399,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_waybel_7(sK5,sK4)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_7373])).

cnf(c_7498,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_waybel_7(sK5,sK4) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7399])).

cnf(c_8,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k13_lattice3(X1,sK2(X1,X0),sK3(X1,X0)),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1222,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k13_lattice3(X1,sK2(X1,X0),sK3(X1,X0)),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_369])).

cnf(c_1223,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(k13_lattice3(X0,sK2(X0,sK5),sK3(X0,sK5)),sK5)
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1222])).

cnf(c_1642,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(k13_lattice3(X0,sK2(X0,sK5),sK3(X0,sK5)),sK5)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1223,c_910])).

cnf(c_1643,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5)),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1642])).

cnf(c_2914,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5)),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2807,c_1643])).

cnf(c_2927,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) != iProver_top
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | r2_hidden(k13_lattice3(k7_lattice3(sK4),sK2(k7_lattice3(sK4),sK5),sK3(k7_lattice3(sK4),sK5)),sK5) = iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2914])).

cnf(c_6,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK3(X1,X0),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1294,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK3(X1,X0),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_369])).

cnf(c_1295,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK3(X0,sK5),sK5)
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1294])).

cnf(c_1580,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK3(X0,sK5),sK5)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1295,c_910])).

cnf(c_1581,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1580])).

cnf(c_2916,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2807,c_1581])).

cnf(c_2923,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) != iProver_top
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | r2_hidden(sK3(k7_lattice3(sK4),sK5),sK5) != iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2916])).

cnf(c_7,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X0),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1258,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(sK2(X1,X0),X0)
    | ~ v1_lattice3(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_369])).

cnf(c_1259,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK2(X0,sK5),sK5)
    | ~ v1_lattice3(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_1258])).

cnf(c_1611,plain,
    ( ~ v2_waybel_0(sK5,X0)
    | ~ v13_waybel_0(sK5,X0)
    | v2_waybel_7(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(sK2(X0,sK5),sK5)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k7_lattice3(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1259,c_910])).

cnf(c_1612,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | ~ v13_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(unflattening,[status(thm)],[c_1611])).

cnf(c_2917,plain,
    ( ~ v2_waybel_0(sK5,k7_lattice3(sK4))
    | v2_waybel_7(sK5,k7_lattice3(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4))))
    | ~ r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5)
    | ~ v3_orders_2(k7_lattice3(sK4))
    | ~ v4_orders_2(k7_lattice3(sK4))
    | ~ v5_orders_2(k7_lattice3(sK4))
    | ~ l1_orders_2(k7_lattice3(sK4)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2807,c_1612])).

cnf(c_2922,plain,
    ( v2_waybel_0(sK5,k7_lattice3(sK4)) != iProver_top
    | v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK4)))) != iProver_top
    | r2_hidden(sK2(k7_lattice3(sK4),sK5),sK5) != iProver_top
    | v3_orders_2(k7_lattice3(sK4)) != iProver_top
    | v4_orders_2(k7_lattice3(sK4)) != iProver_top
    | v5_orders_2(k7_lattice3(sK4)) != iProver_top
    | l1_orders_2(k7_lattice3(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2917])).

cnf(c_38,negated_conjecture,
    ( v2_waybel_7(sK5,k7_lattice3(sK4))
    | v1_waybel_7(sK5,sK4) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_87,plain,
    ( v2_waybel_7(sK5,k7_lattice3(sK4)) = iProver_top
    | v1_waybel_7(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12843,c_12651,c_12626,c_12615,c_12598,c_11790,c_11766,c_10760,c_10746,c_9650,c_9508,c_9449,c_9372,c_9368,c_9325,c_9321,c_9097,c_9090,c_8922,c_8919,c_8871,c_8868,c_7504,c_7498,c_7492,c_7475,c_7472,c_7469,c_7460,c_7450,c_7449,c_7447,c_7439,c_7430,c_4075,c_4037,c_3999,c_3961,c_3923,c_3696,c_2927,c_2923,c_2922,c_2921,c_2920,c_2856,c_87,c_68,c_65,c_64,c_63])).


%------------------------------------------------------------------------------
