%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1981+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:59 EST 2020

% Result     : Theorem 31.02s
% Output     : CNFRefutation 31.02s
% Verified   : 
% Statistics : Number of formulae       :  400 (23309 expanded)
%              Number of clauses        :  266 (5534 expanded)
%              Number of leaves         :   28 (5362 expanded)
%              Depth                    :   44
%              Number of atoms          : 2695 (273515 expanded)
%              Number of equality atoms :  783 (5112 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal clause size      :   36 (   7 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f74,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f74])).

fof(f118,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v7_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( v3_waybel_7(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v11_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v7_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( v3_waybel_7(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f25,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v11_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( v3_waybel_7(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_waybel_7(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_waybel_7(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f61])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_waybel_7(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & v1_subset_1(X1,u1_struct_0(X0))
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( ~ v3_waybel_7(X2,X0)
            | ~ r1_tarski(sK5,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v13_waybel_0(X2,X0)
            | ~ v2_waybel_0(X2,X0)
            | v1_xboole_0(X2) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK5,X0)
        & v2_waybel_0(sK5,X0)
        & v1_subset_1(sK5,u1_struct_0(X0))
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ~ v3_waybel_7(X2,X0)
                | ~ r1_tarski(X1,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v13_waybel_0(X2,X0)
                | ~ v2_waybel_0(X2,X0)
                | v1_xboole_0(X2) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ~ v3_waybel_7(X2,sK4)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
              | ~ v13_waybel_0(X2,sK4)
              | ~ v2_waybel_0(X2,sK4)
              | v1_xboole_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & v13_waybel_0(X1,sK4)
          & v2_waybel_0(X1,sK4)
          & v1_subset_1(X1,u1_struct_0(sK4))
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK4)
      & v2_lattice3(sK4)
      & v1_lattice3(sK4)
      & v11_waybel_1(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,
    ( ! [X2] :
        ( ~ v3_waybel_7(X2,sK4)
        | ~ r1_tarski(sK5,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
        | ~ v13_waybel_0(X2,sK4)
        | ~ v2_waybel_0(X2,sK4)
        | v1_xboole_0(X2) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v13_waybel_0(sK5,sK4)
    & v2_waybel_0(sK5,sK4)
    & v1_subset_1(sK5,u1_struct_0(sK4))
    & ~ v1_xboole_0(sK5)
    & l1_orders_2(sK4)
    & v2_lattice3(sK4)
    & v1_lattice3(sK4)
    & v11_waybel_1(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f62,f78,f77])).

fof(f135,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f79])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f63])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f64,f65])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f139,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f130,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f88,plain,(
    ! [X0] :
      ( v3_yellow_0(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => ( v2_yellow_0(X0)
          & v1_yellow_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => v1_yellow_0(X0) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f30,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f31,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f81,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X0] :
      ( k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f105,plain,(
    ! [X0] :
      ( k5_waybel_0(X0,k3_yellow_0(X0)) = k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    ! [X0] :
      ( v3_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    ! [X0] :
      ( v4_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X0] :
      ( v5_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f127,plain,(
    v11_waybel_1(sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f124,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f125,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f126,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f129,plain,(
    v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f131,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f79])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f7,f67])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f68])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v2_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(X2,X0)
                & v2_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) )
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v13_waybel_0(X3,X0)
                        & v2_waybel_0(X3,X0)
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_subset_1(X1,X3)
                          & r1_tarski(X2,X3)
                          & v2_waybel_7(X3,X0) ) )
                  & r1_subset_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X1,X3)
                  & r1_tarski(X2,X3)
                  & v2_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,X0)
                  & v2_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_subset_1(X1,X3)
                  & r1_tarski(X2,X3)
                  & v2_waybel_7(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,X0)
                  & v2_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f52])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_subset_1(X1,X3)
          & r1_tarski(X2,X3)
          & v2_waybel_7(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X3,X0)
          & v2_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( r1_subset_1(X1,sK2(X0,X1,X2))
        & r1_tarski(X2,sK2(X0,X1,X2))
        & v2_waybel_7(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(sK2(X0,X1,X2),X0)
        & v2_waybel_0(sK2(X0,X1,X2),X0)
        & ~ v1_xboole_0(sK2(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_subset_1(X1,sK2(X0,X1,X2))
                & r1_tarski(X2,sK2(X0,X1,X2))
                & v2_waybel_7(sK2(X0,X1,X2),X0)
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                & v13_waybel_0(sK2(X0,X1,X2),X0)
                & v2_waybel_0(sK2(X0,X1,X2),X0)
                & ~ v1_xboole_0(sK2(X0,X1,X2)) )
              | ~ r1_subset_1(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v13_waybel_0(X2,X0)
              | ~ v2_waybel_0(X2,X0)
              | v1_xboole_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f72])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f89,plain,(
    ! [X0] :
      ( v2_waybel_1(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f128,plain,(
    v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f133,plain,(
    v2_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f134,plain,(
    v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f79])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) = X0
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK0(X0,X1) != X0
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v13_waybel_0(sK2(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_0(sK2(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r1_subset_1(X1,sK2(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(sK2(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_subset_1(X1,u1_struct_0(X0))
              | r2_hidden(k3_yellow_0(X0),X1) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v2_waybel_7(sK2(X0,X1,X2),X0)
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( ( v2_waybel_7(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0)) )
          <=> v3_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0)) )
          <=> v3_waybel_7(X1,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0)) )
          <=> v3_waybel_7(X1,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_waybel_7(X1,X0)
                & v1_subset_1(X1,u1_struct_0(X0)) )
              | ~ v3_waybel_7(X1,X0) )
            & ( v3_waybel_7(X1,X0)
              | ~ v2_waybel_7(X1,X0)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_waybel_7(X1,X0)
                & v1_subset_1(X1,u1_struct_0(X0)) )
              | ~ v3_waybel_7(X1,X0) )
            & ( v3_waybel_7(X1,X0)
              | ~ v2_waybel_7(X1,X0)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f70])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v3_waybel_7(X1,X0)
      | ~ v2_waybel_7(X1,X0)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f136,plain,(
    ! [X2] :
      ( ~ v3_waybel_7(X2,sK4)
      | ~ r1_tarski(sK5,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ v13_waybel_0(X2,sK4)
      | ~ v2_waybel_0(X2,sK4)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK2(X0,X1,X2))
      | ~ r1_subset_1(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X2,X0)
      | ~ v2_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v2_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f137,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f91])).

fof(f138,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f137])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f132,plain,(
    v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f79])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k3_yellow_0(X0),X1)
      | ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_3190,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_3186,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f139])).

cnf(c_3199,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4419,plain,
    ( sK3(X0,k1_tarski(X1)) = X1
    | r1_xboole_0(X0,k1_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_3199])).

cnf(c_21,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_subset_1(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_3196,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8063,plain,
    ( sK3(X0,k1_tarski(X1)) = X1
    | r1_subset_1(X0,k1_tarski(X1)) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4419,c_3196])).

cnf(c_23,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3194,plain,
    ( r1_subset_1(X0,X1) != iProver_top
    | r1_subset_1(X1,X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13636,plain,
    ( sK3(X0,k1_tarski(X1)) = X1
    | r1_subset_1(k1_tarski(X1),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8063,c_3194])).

cnf(c_14,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_50,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1896,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_50])).

cnf(c_1897,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1896])).

cnf(c_3170,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1897])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3197,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5121,plain,
    ( k6_domain_1(u1_struct_0(sK4),k3_yellow_0(sK4)) = k1_tarski(k3_yellow_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_3197])).

cnf(c_3,plain,
    ( ~ v11_waybel_1(X0)
    | v3_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1,plain,
    ( ~ v3_yellow_0(X0)
    | v1_yellow_0(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_612,plain,
    ( ~ v11_waybel_1(X0)
    | v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_3,c_1])).

cnf(c_25,plain,
    ( ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0)) = k5_waybel_0(X0,k3_yellow_0(X0)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_803,plain,
    ( ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0)) = k5_waybel_0(X0,k3_yellow_0(X0)) ),
    inference(resolution,[status(thm)],[c_612,c_25])).

cnf(c_8,plain,
    ( v3_orders_2(X0)
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_7,plain,
    ( v4_orders_2(X0)
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6,plain,
    ( v5_orders_2(X0)
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_807,plain,
    ( ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0)) = k5_waybel_0(X0,k3_yellow_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_803,c_25,c_8,c_7,c_6,c_612])).

cnf(c_53,negated_conjecture,
    ( v11_waybel_1(sK4) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1173,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),k3_yellow_0(X0)) = k5_waybel_0(X0,k3_yellow_0(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_807,c_53])).

cnf(c_1174,plain,
    ( ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | k6_domain_1(u1_struct_0(sK4),k3_yellow_0(sK4)) = k5_waybel_0(sK4,k3_yellow_0(sK4)) ),
    inference(unflattening,[status(thm)],[c_1173])).

cnf(c_56,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_55,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_54,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_51,negated_conjecture,
    ( v2_lattice3(sK4) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_123,plain,
    ( ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_yellow_0(sK4)
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4)
    | k6_domain_1(u1_struct_0(sK4),k3_yellow_0(sK4)) = k5_waybel_0(sK4,k3_yellow_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_175,plain,
    ( ~ v11_waybel_1(sK4)
    | v3_yellow_0(sK4)
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_181,plain,
    ( ~ v3_yellow_0(sK4)
    | v1_yellow_0(sK4)
    | ~ l1_orders_2(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | ~ v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_184,plain,
    ( ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4)
    | ~ v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1176,plain,
    ( k6_domain_1(u1_struct_0(sK4),k3_yellow_0(sK4)) = k5_waybel_0(sK4,k3_yellow_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1174,c_56,c_55,c_54,c_53,c_51,c_50,c_123,c_175,c_181,c_184])).

cnf(c_5124,plain,
    ( k5_waybel_0(sK4,k3_yellow_0(sK4)) = k1_tarski(k3_yellow_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5121,c_1176])).

cnf(c_49,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_64,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_68,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3277,plain,
    ( ~ m1_subset_1(X0,sK5)
    | r2_hidden(X0,sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_3409,plain,
    ( ~ m1_subset_1(sK1(sK5),sK5)
    | r2_hidden(sK1(sK5),sK5)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_3277])).

cnf(c_3410,plain,
    ( m1_subset_1(sK1(sK5),sK5) != iProver_top
    | r2_hidden(sK1(sK5),sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3409])).

cnf(c_16,plain,
    ( m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3628,plain,
    ( m1_subset_1(sK1(sK5),sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3629,plain,
    ( m1_subset_1(sK1(sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3628])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3255,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,sK5)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_4348,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK1(sK5),sK5)
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3255])).

cnf(c_4350,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK1(sK5),sK5) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4348])).

cnf(c_5370,plain,
    ( k5_waybel_0(sK4,k3_yellow_0(sK4)) = k1_tarski(k3_yellow_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5124,c_64,c_68,c_3410,c_3629,c_4350])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1336,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_1337,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(unflattening,[status(thm)],[c_1336])).

cnf(c_1875,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k5_waybel_0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1337,c_51])).

cnf(c_1876,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_1875])).

cnf(c_1880,plain,
    ( m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1876,c_50])).

cnf(c_1881,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_1880])).

cnf(c_3171,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1881])).

cnf(c_32,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r1_subset_1(X2,X0)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_2,plain,
    ( ~ v11_waybel_1(X0)
    | v2_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1191,plain,
    ( v2_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_53])).

cnf(c_1192,plain,
    ( v2_waybel_1(sK4)
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1191])).

cnf(c_178,plain,
    ( ~ v11_waybel_1(sK4)
    | v2_waybel_1(sK4)
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1194,plain,
    ( v2_waybel_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1192,c_53,c_51,c_50,c_178,c_184])).

cnf(c_1620,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r1_subset_1(X2,X0)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_1194])).

cnf(c_1621,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ r1_subset_1(X1,X0)
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1620])).

cnf(c_52,negated_conjecture,
    ( v1_lattice3(sK4) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1625,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ r1_subset_1(X1,X0)
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1621,c_56,c_55,c_54,c_52,c_51,c_50])).

cnf(c_3176,plain,
    ( v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(X1,X0) != iProver_top
    | v1_waybel_0(X1,sK4) != iProver_top
    | v12_waybel_0(X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK4,X1,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1625])).

cnf(c_5122,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,X0,X1)) = k1_tarski(sK2(sK4,X0,X1))
    | v2_waybel_0(X1,sK4) != iProver_top
    | v13_waybel_0(X1,sK4) != iProver_top
    | r1_subset_1(X0,X1) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3176,c_3197])).

cnf(c_9741,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k5_waybel_0(sK4,X0),X1)) = k1_tarski(sK2(sK4,k5_waybel_0(sK4,X0),X1))
    | v2_waybel_0(X1,sK4) != iProver_top
    | v13_waybel_0(X1,sK4) != iProver_top
    | r1_subset_1(k5_waybel_0(sK4,X0),X1) != iProver_top
    | v1_waybel_0(k5_waybel_0(sK4,X0),sK4) != iProver_top
    | v12_waybel_0(k5_waybel_0(sK4,X0),sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_waybel_0(sK4,X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3171,c_5122])).

cnf(c_17,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1295,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_17,c_0])).

cnf(c_1812,plain,
    ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1295,c_55])).

cnf(c_1813,plain,
    ( v12_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1812])).

cnf(c_1817,plain,
    ( v12_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1813,c_51,c_50])).

cnf(c_1819,plain,
    ( v12_waybel_0(k5_waybel_0(sK4,X0),sK4) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1817])).

cnf(c_18,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1275,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0) ),
    inference(resolution,[status(thm)],[c_18,c_0])).

cnf(c_1833,plain,
    ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_lattice3(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1275,c_56])).

cnf(c_1834,plain,
    ( v1_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1833])).

cnf(c_1838,plain,
    ( v1_waybel_0(k5_waybel_0(sK4,X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1834,c_51,c_50])).

cnf(c_1840,plain,
    ( v1_waybel_0(k5_waybel_0(sK4,X0),sK4) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1838])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1315,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(unflattening,[status(thm)],[c_1315])).

cnf(c_1851,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_xboole_0(k5_waybel_0(X1,X0))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1316,c_56])).

cnf(c_1852,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v1_xboole_0(k5_waybel_0(sK4,X0))
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1851])).

cnf(c_1856,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK4))
    | ~ v1_xboole_0(k5_waybel_0(sK4,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1852,c_51,c_50])).

cnf(c_1858,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(k5_waybel_0(sK4,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1856])).

cnf(c_10527,plain,
    ( v1_xboole_0(X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_subset_1(k5_waybel_0(sK4,X0),X1) != iProver_top
    | v13_waybel_0(X1,sK4) != iProver_top
    | v2_waybel_0(X1,sK4) != iProver_top
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k5_waybel_0(sK4,X0),X1)) = k1_tarski(sK2(sK4,k5_waybel_0(sK4,X0),X1))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9741,c_1819,c_1840,c_1858])).

cnf(c_10528,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k5_waybel_0(sK4,X0),X1)) = k1_tarski(sK2(sK4,k5_waybel_0(sK4,X0),X1))
    | v2_waybel_0(X1,sK4) != iProver_top
    | v13_waybel_0(X1,sK4) != iProver_top
    | r1_subset_1(k5_waybel_0(sK4,X0),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_10527])).

cnf(c_10534,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4)),X0)) = k1_tarski(sK2(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4)),X0))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5370,c_10528])).

cnf(c_10535,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10534,c_5370])).

cnf(c_63,plain,
    ( l1_orders_2(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_153,plain,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_155,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_3172,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(k5_waybel_0(sK4,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1856])).

cnf(c_3626,plain,
    ( v1_xboole_0(k5_waybel_0(sK4,k3_yellow_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3170,c_3172])).

cnf(c_5372,plain,
    ( v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5370,c_3626])).

cnf(c_3174,plain,
    ( v12_waybel_0(k5_waybel_0(sK4,X0),sK4) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1817])).

cnf(c_5379,plain,
    ( v12_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) = iProver_top
    | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5370,c_3174])).

cnf(c_3173,plain,
    ( v1_waybel_0(k5_waybel_0(sK4,X0),sK4) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1838])).

cnf(c_5380,plain,
    ( v1_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) = iProver_top
    | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5370,c_3173])).

cnf(c_5378,plain,
    ( m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k1_tarski(k3_yellow_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5370,c_3171])).

cnf(c_5768,plain,
    ( m1_subset_1(k1_tarski(k3_yellow_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5378,c_63,c_155])).

cnf(c_9745,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | v1_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | v12_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5768,c_5122])).

cnf(c_10819,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v2_waybel_0(X0,sK4) != iProver_top
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10535,c_63,c_155,c_5372,c_5379,c_5380,c_9745])).

cnf(c_10820,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_10819])).

cnf(c_13759,plain,
    ( sK3(X0,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4)
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13636,c_10820])).

cnf(c_14332,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v2_waybel_0(X0,sK4) != iProver_top
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))
    | sK3(X0,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13759,c_5372])).

cnf(c_14333,plain,
    ( sK3(X0,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4)
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_14332])).

cnf(c_14339,plain,
    ( sK3(sK5,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4)
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5))
    | v2_waybel_0(sK5,sK4) != iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_14333])).

cnf(c_47,negated_conjecture,
    ( v2_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_66,plain,
    ( v2_waybel_0(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v13_waybel_0(sK5,sK4) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_67,plain,
    ( v13_waybel_0(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_14740,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5))
    | sK3(sK5,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14339,c_64,c_66,c_67])).

cnf(c_14741,plain,
    ( sK3(sK5,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4)
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_14740])).

cnf(c_11,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | sK0(X0,X1) = X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3201,plain,
    ( sK0(X0,X1) = X0
    | k1_tarski(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_24,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3193,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5169,plain,
    ( sK0(X0,X1) = X0
    | k1_tarski(X0) = X1
    | m1_subset_1(sK0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3201,c_3193])).

cnf(c_3188,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_9315,plain,
    ( sK0(X0,k1_zfmisc_1(X1)) = X0
    | k1_zfmisc_1(X1) = k1_tarski(X0)
    | r2_hidden(X2,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5169,c_3188])).

cnf(c_15815,plain,
    ( sK0(X0,sK0(X1,k1_zfmisc_1(X2))) = X0
    | sK0(X1,k1_zfmisc_1(X2)) = X1
    | sK0(X1,k1_zfmisc_1(X2)) = k1_tarski(X0)
    | k1_zfmisc_1(X2) = k1_tarski(X1)
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3201,c_9315])).

cnf(c_18448,plain,
    ( sK3(sK5,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4)
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5))
    | sK0(X0,sK0(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) = X0
    | sK0(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = X1
    | sK0(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = k1_tarski(X0)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))) = k1_tarski(X1) ),
    inference(superposition,[status(thm)],[c_14741,c_15815])).

cnf(c_10,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | sK0(X0,X1) != X0
    | k1_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3202,plain,
    ( sK0(X0,X1) != X0
    | k1_tarski(X0) = X1
    | r2_hidden(sK0(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18733,plain,
    ( sK3(sK5,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4)
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5))
    | sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = X0
    | sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = k1_tarski(X1)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))) = k1_tarski(X0)
    | r2_hidden(sK0(X1,sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18448,c_3202])).

cnf(c_19961,plain,
    ( sK3(sK5,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4)
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5))
    | sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = X0
    | sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = k1_tarski(X1)
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))) = k1_tarski(X0)
    | r2_hidden(X1,sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18448,c_18733])).

cnf(c_20335,plain,
    ( sK3(sK5,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4)
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5))
    | sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = X0
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))) = k1_tarski(X0)
    | k1_tarski(sK3(X1,sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))))) = sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r1_xboole_0(X1,sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_19961])).

cnf(c_44539,plain,
    ( sK3(sK5,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4)
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5))
    | sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = X0
    | k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))) = k1_tarski(X0)
    | k1_tarski(sK3(X1,sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))))) = sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r1_subset_1(X1,sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK0(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_20335,c_3196])).

cnf(c_33,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(sK2(X1,X2,X0),X1)
    | ~ r1_subset_1(X2,X0)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1578,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(sK2(X1,X2,X0),X1)
    | ~ r1_subset_1(X2,X0)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_1194])).

cnf(c_1579,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | v13_waybel_0(sK2(sK4,X1,X0),sK4)
    | ~ r1_subset_1(X1,X0)
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1578])).

cnf(c_1583,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | v13_waybel_0(sK2(sK4,X1,X0),sK4)
    | ~ r1_subset_1(X1,X0)
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1579,c_56,c_55,c_54,c_52,c_51,c_50])).

cnf(c_3177,plain,
    ( v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,X1,X0),sK4) = iProver_top
    | r1_subset_1(X1,X0) != iProver_top
    | v1_waybel_0(X1,sK4) != iProver_top
    | v12_waybel_0(X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1583])).

cnf(c_34,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_0(sK2(X1,X2,X0),X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r1_subset_1(X2,X0)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1536,plain,
    ( ~ v2_waybel_0(X0,X1)
    | v2_waybel_0(sK2(X1,X2,X0),X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r1_subset_1(X2,X0)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_1194])).

cnf(c_1537,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | v2_waybel_0(sK2(sK4,X1,X0),sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ r1_subset_1(X1,X0)
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1536])).

cnf(c_1541,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | v2_waybel_0(sK2(sK4,X1,X0),sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ r1_subset_1(X1,X0)
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1537,c_56,c_55,c_54,c_52,c_51,c_50])).

cnf(c_3178,plain,
    ( v2_waybel_0(X0,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,X1,X0),sK4) = iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(X1,X0) != iProver_top
    | v1_waybel_0(X1,sK4) != iProver_top
    | v12_waybel_0(X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1541])).

cnf(c_29,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r1_subset_1(X2,X0)
    | r1_subset_1(X2,sK2(X1,X2,X0))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1704,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r1_subset_1(X2,X0)
    | r1_subset_1(X2,sK2(X1,X2,X0))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_1194])).

cnf(c_1705,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ r1_subset_1(X1,X0)
    | r1_subset_1(X1,sK2(sK4,X1,X0))
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1704])).

cnf(c_1709,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ r1_subset_1(X1,X0)
    | r1_subset_1(X1,sK2(sK4,X1,X0))
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1705,c_56,c_55,c_54,c_52,c_51,c_50])).

cnf(c_3175,plain,
    ( v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(X1,X0) != iProver_top
    | r1_subset_1(X1,sK2(sK4,X1,X0)) = iProver_top
    | v1_waybel_0(X1,sK4) != iProver_top
    | v12_waybel_0(X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1709])).

cnf(c_10825,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | v1_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | v12_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_tarski(k3_yellow_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3175,c_10820])).

cnf(c_10533,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k5_waybel_0(sK4,X0),sK2(sK4,k5_waybel_0(sK4,X0),X1))) = k1_tarski(sK2(sK4,k5_waybel_0(sK4,X0),sK2(sK4,k5_waybel_0(sK4,X0),X1)))
    | v2_waybel_0(X1,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,k5_waybel_0(sK4,X0),X1),sK4) != iProver_top
    | v13_waybel_0(X1,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k5_waybel_0(sK4,X0),X1),sK4) != iProver_top
    | r1_subset_1(k5_waybel_0(sK4,X0),X1) != iProver_top
    | v1_waybel_0(k5_waybel_0(sK4,X0),sK4) != iProver_top
    | v12_waybel_0(k5_waybel_0(sK4,X0),sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2(sK4,k5_waybel_0(sK4,X0),X1),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK2(sK4,k5_waybel_0(sK4,X0),X1)) = iProver_top
    | v1_xboole_0(k5_waybel_0(sK4,X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3175,c_10528])).

cnf(c_1877,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k5_waybel_0(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_orders_2(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1876])).

cnf(c_42004,plain,
    ( v1_xboole_0(sK2(sK4,k5_waybel_0(sK4,X0),X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k5_waybel_0(sK4,X0),sK2(sK4,k5_waybel_0(sK4,X0),X1))) = k1_tarski(sK2(sK4,k5_waybel_0(sK4,X0),sK2(sK4,k5_waybel_0(sK4,X0),X1)))
    | v2_waybel_0(X1,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,k5_waybel_0(sK4,X0),X1),sK4) != iProver_top
    | v13_waybel_0(X1,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k5_waybel_0(sK4,X0),X1),sK4) != iProver_top
    | r1_subset_1(k5_waybel_0(sK4,X0),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2(sK4,k5_waybel_0(sK4,X0),X1),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10533,c_63,c_1819,c_1840,c_1858,c_1877])).

cnf(c_42005,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k5_waybel_0(sK4,X0),sK2(sK4,k5_waybel_0(sK4,X0),X1))) = k1_tarski(sK2(sK4,k5_waybel_0(sK4,X0),sK2(sK4,k5_waybel_0(sK4,X0),X1)))
    | v2_waybel_0(X1,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,k5_waybel_0(sK4,X0),X1),sK4) != iProver_top
    | v13_waybel_0(X1,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k5_waybel_0(sK4,X0),X1),sK4) != iProver_top
    | r1_subset_1(k5_waybel_0(sK4,X0),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(sK2(sK4,k5_waybel_0(sK4,X0),X1),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK2(sK4,k5_waybel_0(sK4,X0),X1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_42004])).

cnf(c_42011,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4)),sK2(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4)),sK2(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | r1_subset_1(k5_waybel_0(sK4,k3_yellow_0(sK4)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,k5_waybel_0(sK4,k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5370,c_42005])).

cnf(c_42012,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k3_yellow_0(sK4),u1_struct_0(sK4)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42011,c_5370])).

cnf(c_42705,plain,
    ( m1_subset_1(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | v13_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | v2_waybel_0(X0,sK4) != iProver_top
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_42012,c_63,c_155,c_5372,c_5378,c_5379,c_5380,c_10825])).

cnf(c_42706,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_42705])).

cnf(c_42711,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | v1_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | v12_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_tarski(k3_yellow_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3176,c_42706])).

cnf(c_49296,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | v13_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | v2_waybel_0(X0,sK4) != iProver_top
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10825,c_63,c_155,c_5372,c_5378,c_5379,c_5380,c_42711])).

cnf(c_49297,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_49296])).

cnf(c_49302,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | v1_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | v12_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_tarski(k3_yellow_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3178,c_49297])).

cnf(c_55400,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49302,c_63,c_155,c_5372,c_5378,c_5379,c_5380])).

cnf(c_55401,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0),sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_55400])).

cnf(c_55406,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | v1_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | v12_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_tarski(k3_yellow_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3177,c_55401])).

cnf(c_55507,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55406,c_63,c_155,c_5372,c_5378,c_5379,c_5380])).

cnf(c_55508,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)))
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),X0)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(renaming,[status(thm)],[c_55507])).

cnf(c_35,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r1_subset_1(X2,X0)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2(X1,X2,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1494,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r1_subset_1(X2,X0)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(sK2(X1,X2,X0))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_1194])).

cnf(c_1495,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ r1_subset_1(X1,X0)
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(sK2(sK4,X1,X0))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1494])).

cnf(c_1499,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ r1_subset_1(X1,X0)
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(sK2(sK4,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1495,c_56,c_55,c_54,c_52,c_51,c_50])).

cnf(c_3179,plain,
    ( v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(X1,X0) != iProver_top
    | v1_waybel_0(X1,sK4) != iProver_top
    | v12_waybel_0(X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK2(sK4,X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1499])).

cnf(c_6195,plain,
    ( v2_waybel_0(sK5,sK4) != iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | r1_subset_1(X0,sK5) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,X0,sK5)) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3186,c_3179])).

cnf(c_6215,plain,
    ( v1_xboole_0(sK2(sK4,X0,sK5)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6195,c_64,c_66,c_67])).

cnf(c_6216,plain,
    ( r1_subset_1(X0,sK5) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,X0,sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6215])).

cnf(c_6225,plain,
    ( r1_subset_1(k1_tarski(k3_yellow_0(sK4)),sK5) != iProver_top
    | v1_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | v12_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)) != iProver_top
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5768,c_6216])).

cnf(c_6314,plain,
    ( v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6225,c_63,c_155,c_5372,c_5379,c_5380])).

cnf(c_6315,plain,
    ( r1_subset_1(k1_tarski(k3_yellow_0(sK4)),sK5) != iProver_top
    | v1_xboole_0(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6314])).

cnf(c_55520,plain,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5))) = k1_tarski(sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK2(sK4,k1_tarski(k3_yellow_0(sK4)),sK5)))
    | v2_waybel_0(sK5,sK4) != iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),sK5) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_55508,c_6315])).

cnf(c_42,plain,
    ( v1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k3_yellow_0(X1),X0)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_867,plain,
    ( v1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k3_yellow_0(X1),X0)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_612,c_42])).

cnf(c_868,plain,
    ( v1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k3_yellow_0(X1),X0)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_867])).

cnf(c_896,plain,
    ( v1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k3_yellow_0(X1),X0)
    | v1_xboole_0(X0)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_868,c_6,c_7,c_8])).

cnf(c_1202,plain,
    ( v1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(k3_yellow_0(X1),X0)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_896,c_53])).

cnf(c_1203,plain,
    ( v1_subset_1(X0,u1_struct_0(sK4))
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k3_yellow_0(sK4),X0)
    | v1_xboole_0(X0)
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1202])).

cnf(c_1207,plain,
    ( v1_subset_1(X0,u1_struct_0(sK4))
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k3_yellow_0(sK4),X0)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1203,c_51,c_50,c_184])).

cnf(c_3181,plain,
    ( v1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_5107,plain,
    ( v1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4)) = iProver_top
    | v2_waybel_0(X1,sK4) != iProver_top
    | v2_waybel_0(sK2(sK4,X0,X1),sK4) != iProver_top
    | v13_waybel_0(X1,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,X0,X1),sK4) != iProver_top
    | r1_subset_1(X0,X1) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK2(sK4,X0,X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3176,c_3181])).

cnf(c_31,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(sK2(X1,X2,X0),X1)
    | ~ r1_subset_1(X2,X0)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_28,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v3_waybel_7(X0,X1)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_44,negated_conjecture,
    ( ~ r1_tarski(sK5,X0)
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ v3_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1002,plain,
    ( ~ r1_tarski(sK5,X0)
    | ~ v1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_waybel_0(X1,X2)
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X1,X2)
    | ~ v13_waybel_0(X0,sK4)
    | ~ v2_waybel_7(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v11_waybel_1(X2)
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(X2)
    | X0 != X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_44])).

cnf(c_1003,plain,
    ( ~ r1_tarski(sK5,X0)
    | ~ v1_subset_1(X0,u1_struct_0(sK4))
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ v2_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v11_waybel_1(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1002])).

cnf(c_1007,plain,
    ( v1_xboole_0(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v2_waybel_7(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ v2_waybel_0(X0,sK4)
    | ~ v1_subset_1(X0,u1_struct_0(sK4))
    | ~ r1_tarski(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1003,c_56,c_55,c_54,c_53,c_52,c_51,c_50])).

cnf(c_1008,plain,
    ( ~ r1_tarski(sK5,X0)
    | ~ v1_subset_1(X0,u1_struct_0(sK4))
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ v2_waybel_7(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1007])).

cnf(c_1043,plain,
    ( ~ r1_tarski(sK5,X0)
    | ~ v1_subset_1(X0,u1_struct_0(sK4))
    | ~ v2_waybel_0(X1,X2)
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X1,X2)
    | ~ v13_waybel_0(X0,sK4)
    | ~ r1_subset_1(X3,X1)
    | ~ v1_waybel_0(X3,X2)
    | ~ v12_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_waybel_1(X2)
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(X2)
    | sK2(X2,X3,X1) != X0
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1008])).

cnf(c_1044,plain,
    ( ~ r1_tarski(sK5,sK2(sK4,X0,X1))
    | ~ v1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v2_waybel_0(X1,sK4)
    | ~ v2_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ v13_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2(sK4,X0,X1))
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ v2_waybel_1(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1043])).

cnf(c_1048,plain,
    ( v1_xboole_0(sK2(sK4,X0,X1))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v12_waybel_0(X0,sK4)
    | ~ v1_waybel_0(X0,sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v13_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ v2_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4))
    | ~ r1_tarski(sK5,sK2(sK4,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1044,c_56,c_55,c_54,c_53,c_52,c_51,c_50,c_178,c_184])).

cnf(c_1049,plain,
    ( ~ r1_tarski(sK5,sK2(sK4,X0,X1))
    | ~ v1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v2_waybel_0(X1,sK4)
    | ~ v2_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ v13_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK2(sK4,X0,X1)) ),
    inference(renaming,[status(thm)],[c_1048])).

cnf(c_30,plain,
    ( r1_tarski(X0,sK2(X1,X2,X0))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r1_subset_1(X2,X0)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1662,plain,
    ( r1_tarski(X0,sK2(X1,X2,X0))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r1_subset_1(X2,X0)
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1194])).

cnf(c_1663,plain,
    ( r1_tarski(X0,sK2(sK4,X1,X0))
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ r1_subset_1(X1,X0)
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v1_lattice3(sK4)
    | ~ l1_orders_2(sK4)
    | ~ v2_lattice3(sK4) ),
    inference(unflattening,[status(thm)],[c_1662])).

cnf(c_1667,plain,
    ( r1_tarski(X0,sK2(sK4,X1,X0))
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ r1_subset_1(X1,X0)
    | ~ v1_waybel_0(X1,sK4)
    | ~ v12_waybel_0(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1663,c_56,c_55,c_54,c_52,c_51,c_50])).

cnf(c_1905,plain,
    ( ~ v1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v2_waybel_0(X2,sK4)
    | ~ v2_waybel_0(X1,sK4)
    | ~ v2_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v13_waybel_0(X2,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ v13_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ r1_subset_1(X3,X2)
    | ~ v1_waybel_0(X3,sK4)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X3,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(sK2(sK4,X0,X1))
    | sK2(sK4,X3,X2) != sK2(sK4,X0,X1)
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1049,c_1667])).

cnf(c_1906,plain,
    ( ~ v1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v2_waybel_0(X1,sK4)
    | ~ v2_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v2_waybel_0(sK5,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ v13_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v13_waybel_0(sK5,sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ r1_subset_1(X2,sK5)
    | ~ v1_waybel_0(X2,sK4)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X2,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(sK2(sK4,X0,X1))
    | v1_xboole_0(sK5)
    | sK2(sK4,X2,sK5) != sK2(sK4,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1905])).

cnf(c_1910,plain,
    ( v1_xboole_0(sK2(sK4,X0,X1))
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v13_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ v1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v2_waybel_0(X1,sK4)
    | ~ v2_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ r1_subset_1(X2,sK5)
    | ~ v1_waybel_0(X2,sK4)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X2,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | sK2(sK4,X2,sK5) != sK2(sK4,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1906,c_49,c_47,c_46,c_45])).

cnf(c_1911,plain,
    ( ~ v1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v2_waybel_0(X1,sK4)
    | ~ v2_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ v13_waybel_0(sK2(sK4,X0,X1),sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ r1_subset_1(X2,sK5)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v1_waybel_0(X2,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X2,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK2(sK4,X0,X1),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(sK2(sK4,X0,X1))
    | sK2(sK4,X2,sK5) != sK2(sK4,X0,X1) ),
    inference(renaming,[status(thm)],[c_1910])).

cnf(c_1956,plain,
    ( ~ v1_subset_1(sK2(sK4,X0,X1),u1_struct_0(sK4))
    | ~ v2_waybel_0(X1,sK4)
    | ~ v13_waybel_0(X1,sK4)
    | ~ r1_subset_1(X0,X1)
    | ~ r1_subset_1(X2,sK5)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v1_waybel_0(X2,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X2,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | sK2(sK4,X2,sK5) != sK2(sK4,X0,X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1911,c_1499,c_1625,c_1583,c_1541])).

cnf(c_3169,plain,
    ( sK2(sK4,X0,sK5) != sK2(sK4,X1,X2)
    | v1_subset_1(sK2(sK4,X1,X2),u1_struct_0(sK4)) != iProver_top
    | v2_waybel_0(X2,sK4) != iProver_top
    | v13_waybel_0(X2,sK4) != iProver_top
    | r1_subset_1(X1,X2) != iProver_top
    | r1_subset_1(X0,sK5) != iProver_top
    | v1_waybel_0(X1,sK4) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X1,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1956])).

cnf(c_3667,plain,
    ( v1_subset_1(sK2(sK4,X0,sK5),u1_struct_0(sK4)) != iProver_top
    | v2_waybel_0(sK5,sK4) != iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | r1_subset_1(X0,sK5) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3169])).

cnf(c_6492,plain,
    ( v1_xboole_0(X0) = iProver_top
    | v1_subset_1(sK2(sK4,X0,sK5),u1_struct_0(sK4)) != iProver_top
    | r1_subset_1(X0,sK5) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3667,c_64,c_66,c_67,c_68])).

cnf(c_6493,plain,
    ( v1_subset_1(sK2(sK4,X0,sK5),u1_struct_0(sK4)) != iProver_top
    | r1_subset_1(X0,sK5) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6492])).

cnf(c_7362,plain,
    ( v2_waybel_0(sK2(sK4,X0,sK5),sK4) != iProver_top
    | v2_waybel_0(sK5,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,X0,sK5),sK4) != iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | r1_subset_1(X0,sK5) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK2(sK4,X0,sK5)) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2(sK4,X0,sK5)) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5107,c_6493])).

cnf(c_3754,plain,
    ( v2_waybel_0(sK2(sK4,X0,sK5),sK4)
    | ~ v2_waybel_0(sK5,sK4)
    | ~ v13_waybel_0(sK5,sK4)
    | ~ r1_subset_1(X0,sK5)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1541])).

cnf(c_3755,plain,
    ( v2_waybel_0(sK2(sK4,X0,sK5),sK4) = iProver_top
    | v2_waybel_0(sK5,sK4) != iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | r1_subset_1(X0,sK5) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3754])).

cnf(c_3769,plain,
    ( ~ v2_waybel_0(sK5,sK4)
    | v13_waybel_0(sK2(sK4,X0,sK5),sK4)
    | ~ v13_waybel_0(sK5,sK4)
    | ~ r1_subset_1(X0,sK5)
    | ~ v1_waybel_0(X0,sK4)
    | ~ v12_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_3770,plain,
    ( v2_waybel_0(sK5,sK4) != iProver_top
    | v13_waybel_0(sK2(sK4,X0,sK5),sK4) = iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | r1_subset_1(X0,sK5) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3769])).

cnf(c_13397,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK2(sK4,X0,sK5)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7362,c_64,c_66,c_67,c_68,c_3755,c_3770,c_6216])).

cnf(c_13398,plain,
    ( r1_subset_1(X0,sK5) != iProver_top
    | v1_waybel_0(X0,sK4) != iProver_top
    | v12_waybel_0(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK2(sK4,X0,sK5)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_13397])).

cnf(c_22,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_subset_1(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3195,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_129,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_39,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_3189,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK3(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_41,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_3187,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_4325,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3189,c_3187])).

cnf(c_4421,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_3187])).

cnf(c_6040,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_subset_1(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3195,c_129,c_4325,c_4421])).

cnf(c_6046,plain,
    ( v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_xboole_0(X1,sK2(sK4,X1,X0)) = iProver_top
    | r1_subset_1(X1,X0) != iProver_top
    | v1_waybel_0(X1,sK4) != iProver_top
    | v12_waybel_0(X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3175,c_6040])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_3200,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_37,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_3191,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5346,plain,
    ( r1_xboole_0(k1_tarski(X0),X1) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3200,c_3191])).

cnf(c_11067,plain,
    ( v2_waybel_0(X0,sK4) != iProver_top
    | v13_waybel_0(X0,sK4) != iProver_top
    | r1_subset_1(k1_tarski(X1),X0) != iProver_top
    | v1_waybel_0(k1_tarski(X1),sK4) != iProver_top
    | v12_waybel_0(k1_tarski(X1),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X1,sK2(sK4,k1_tarski(X1),X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6046,c_5346])).

cnf(c_54311,plain,
    ( v2_waybel_0(sK5,sK4) != iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | r1_subset_1(k1_tarski(k3_yellow_0(sK4)),sK5) != iProver_top
    | v1_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | v12_waybel_0(k1_tarski(k3_yellow_0(sK4)),sK4) != iProver_top
    | m1_subset_1(k1_tarski(k3_yellow_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_13398,c_11067])).

cnf(c_55552,plain,
    ( r1_subset_1(k1_tarski(k3_yellow_0(sK4)),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55520,c_63,c_64,c_66,c_67,c_68,c_155,c_5372,c_5378,c_5379,c_5380,c_54311])).

cnf(c_55561,plain,
    ( sK3(sK5,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4)
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_13636,c_55552])).

cnf(c_65746,plain,
    ( sK3(sK5,k1_tarski(k3_yellow_0(sK4))) = k3_yellow_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44539,c_64,c_5372,c_55561])).

cnf(c_65755,plain,
    ( r1_xboole_0(sK5,k1_tarski(k3_yellow_0(sK4))) = iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_65746,c_3189])).

cnf(c_48,negated_conjecture,
    ( v1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_43,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_826,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_612,c_43])).

cnf(c_827,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_826])).

cnf(c_855,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_827,c_6,c_7,c_8,c_41])).

cnf(c_1232,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(X1))
    | ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(k3_yellow_0(X1),X0)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_855,c_53])).

cnf(c_1233,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(sK4))
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k3_yellow_0(sK4),X0)
    | ~ l1_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(unflattening,[status(thm)],[c_1232])).

cnf(c_1237,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(sK4))
    | ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k3_yellow_0(sK4),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1233,c_51,c_50,c_184])).

cnf(c_1378,plain,
    ( ~ v2_waybel_0(X0,sK4)
    | ~ v13_waybel_0(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k3_yellow_0(sK4),X0)
    | u1_struct_0(sK4) != u1_struct_0(sK4)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_1237])).

cnf(c_1379,plain,
    ( ~ v2_waybel_0(sK5,sK4)
    | ~ v13_waybel_0(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(k3_yellow_0(sK4),sK5) ),
    inference(unflattening,[status(thm)],[c_1378])).

cnf(c_1380,plain,
    ( v2_waybel_0(sK5,sK4) != iProver_top
    | v13_waybel_0(sK5,sK4) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k3_yellow_0(sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1379])).

cnf(c_65764,plain,
    ( r1_xboole_0(sK5,k1_tarski(k3_yellow_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_65755,c_66,c_67,c_68,c_1380])).

cnf(c_65769,plain,
    ( r1_subset_1(sK5,k1_tarski(k3_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_65764,c_3196])).

cnf(c_66435,plain,
    ( r1_subset_1(sK5,k1_tarski(k3_yellow_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_65769,c_64,c_5372])).

cnf(c_66440,plain,
    ( r1_subset_1(k1_tarski(k3_yellow_0(sK4)),sK5) = iProver_top
    | v1_xboole_0(k1_tarski(k3_yellow_0(sK4))) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_66435,c_3194])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66440,c_54311,c_5380,c_5379,c_5378,c_5372,c_155,c_68,c_67,c_66,c_64,c_63])).


%------------------------------------------------------------------------------
