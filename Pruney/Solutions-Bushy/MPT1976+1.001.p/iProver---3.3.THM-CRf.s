%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1976+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:58 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3897)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0))
        & v2_waybel_0(X1,k3_yellow_1(X0))
        & ~ v1_xboole_0(X1) )
     => ( v2_waybel_7(X1,k3_yellow_1(X0))
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r2_hidden(k6_subset_1(X0,X2),X1)
              | r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & ~ v1_xboole_0(X1) )
       => ( v2_waybel_7(X1,k3_yellow_1(X0))
        <=> ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(X0))
             => ( r2_hidden(k6_subset_1(X0,X2),X1)
                | r2_hidden(X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_7(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_7(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
      & ( ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | v2_waybel_7(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
      & ( ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | v2_waybel_7(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
      & ( ! [X3] :
            ( r2_hidden(k6_subset_1(X0,X3),X1)
            | r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | v2_waybel_7(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(rectify,[],[f39])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
          & ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r2_hidden(k6_subset_1(X0,sK3),X1)
        & ~ r2_hidden(sK3,X1)
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( ? [X2] :
              ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(X0)) )
          | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
        & ( ! [X3] :
              ( r2_hidden(k6_subset_1(X0,X3),X1)
              | r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | v2_waybel_7(X1,k3_yellow_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0))
        & v2_waybel_0(X1,k3_yellow_1(X0))
        & ~ v1_xboole_0(X1) )
   => ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(sK1,X2),sK2)
            & ~ r2_hidden(X2,sK2)
            & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
        | ~ v2_waybel_7(sK2,k3_yellow_1(sK1)) )
      & ( ! [X3] :
            ( r2_hidden(k6_subset_1(sK1,X3),sK2)
            | r2_hidden(X3,sK2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK1)) )
        | v2_waybel_7(sK2,k3_yellow_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK1))))
      & v13_waybel_0(sK2,k3_yellow_1(sK1))
      & v2_waybel_0(sK2,k3_yellow_1(sK1))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ( ~ r2_hidden(k6_subset_1(sK1,sK3),sK2)
        & ~ r2_hidden(sK3,sK2)
        & m1_subset_1(sK3,k1_zfmisc_1(sK1)) )
      | ~ v2_waybel_7(sK2,k3_yellow_1(sK1)) )
    & ( ! [X3] :
          ( r2_hidden(k6_subset_1(sK1,X3),sK2)
          | r2_hidden(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK1)) )
      | v2_waybel_7(sK2,k3_yellow_1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK1))))
    & v13_waybel_0(sK2,k3_yellow_1(sK1))
    & v2_waybel_0(sK2,k3_yellow_1(sK1))
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f42,f41])).

fof(f76,plain,(
    ! [X3] :
      ( r2_hidden(k6_subset_1(sK1,X3),sK2)
      | r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | v2_waybel_7(sK2,k3_yellow_1(sK1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k2_yellow_1(k9_setfam_1(X0)) = k3_yellow_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : g1_orders_2(X0,k1_yellow_1(X0)) = k2_yellow_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f80,plain,(
    ! [X0] : g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) = k3_yellow_1(X0) ),
    inference(definition_unfolding,[],[f69,f51])).

fof(f101,plain,(
    ! [X3] :
      ( r2_hidden(k6_subset_1(sK1,X3),sK2)
      | r2_hidden(X3,sK2)
      | ~ m1_subset_1(X3,k9_setfam_1(sK1))
      | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) ) ),
    inference(definition_unfolding,[],[f76,f64,f80])).

fof(f73,plain,(
    v2_waybel_0(sK2,k3_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,(
    v2_waybel_0(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) ),
    inference(definition_unfolding,[],[f73,f80])).

fof(f74,plain,(
    v13_waybel_0(sK2,k3_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f103,plain,(
    v13_waybel_0(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) ),
    inference(definition_unfolding,[],[f74,f80])).

fof(f10,axiom,(
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
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(k7_waybel_1(X0,X2),X1)
                  | r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
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
    inference(flattening,[],[f28])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                  & ~ r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k7_waybel_1(X0,X2),X1)
                  | r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
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
    inference(nnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                  & ~ r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k7_waybel_1(X0,X3),X1)
                  | r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
          & ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k7_waybel_1(X0,sK0(X0,X1)),X1)
        & ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ( ~ r2_hidden(k7_waybel_1(X0,sK0(X0,X1)),X1)
                & ~ r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k7_waybel_1(X0,X3),X1)
                  | r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
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
    inference(definition_unfolding,[],[f66,f64])).

fof(f2,axiom,(
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

fof(f20,plain,(
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
    inference(pure_predicate_removal,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f50,plain,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f90,plain,(
    ! [X0] : ~ v2_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f57,f80])).

fof(f6,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f84,plain,(
    ! [X0] : v11_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f56,f80])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f54,f51])).

fof(f49,plain,(
    ! [X0] :
      ( v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f86,plain,(
    ! [X0] : v5_orders_2(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f61,f80])).

fof(f60,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    ! [X0] : v4_orders_2(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f60,f80])).

fof(f59,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f88,plain,(
    ! [X0] : v3_orders_2(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(definition_unfolding,[],[f59,f80])).

fof(f72,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f102,plain,(
    m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))))) ),
    inference(definition_unfolding,[],[f75,f64,f80])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => k7_waybel_1(k3_yellow_1(X0),X1) = k6_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_waybel_1(k3_yellow_1(X0),X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k7_waybel_1(k3_yellow_1(X0),X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))) ) ),
    inference(definition_unfolding,[],[f71,f80,f80])).

fof(f77,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ v2_waybel_7(sK2,k3_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,
    ( m1_subset_1(sK3,k9_setfam_1(sK1))
    | ~ v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) ),
    inference(definition_unfolding,[],[f77,f64,f80])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f83,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k9_setfam_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(definition_unfolding,[],[f62,f64])).

fof(f4,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k9_setfam_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f52,f64])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(k7_waybel_1(X0,sK0(X0,X1)),X1)
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
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(k7_waybel_1(X0,sK0(X0,X1)),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
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
    inference(definition_unfolding,[],[f68,f64])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK0(X0,X1),X1)
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
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
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
    inference(definition_unfolding,[],[f67,f64])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k7_waybel_1(X0,X3),X1)
      | r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_waybel_7(X1,X0)
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
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k7_waybel_1(X0,X3),X1)
      | r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
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
    inference(definition_unfolding,[],[f65,f64])).

fof(f78,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ v2_waybel_7(sK2,k3_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) ),
    inference(definition_unfolding,[],[f78,f80])).

fof(f79,plain,
    ( ~ r2_hidden(k6_subset_1(sK1,sK3),sK2)
    | ~ v2_waybel_7(sK2,k3_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f98,plain,
    ( ~ r2_hidden(k6_subset_1(sK1,sK3),sK2)
    | ~ v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) ),
    inference(definition_unfolding,[],[f79,f80])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(X0,sK2)
    | r2_hidden(k6_subset_1(sK1,X0),sK2)
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))))
    | ~ m1_subset_1(X0,k9_setfam_1(sK1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2260,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k6_subset_1(sK1,X0),sK2) = iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top
    | m1_subset_1(X0,k9_setfam_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_31,negated_conjecture,
    ( v2_waybel_0(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_30,negated_conjecture,
    ( v13_waybel_0(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_21,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v11_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ v11_waybel_1(X0)
    | v2_lattice3(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_16,plain,
    ( ~ v2_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_404,plain,
    ( ~ v11_waybel_1(X0)
    | v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_16])).

cnf(c_405,plain,
    ( ~ v11_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | v2_lattice3(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_10,plain,
    ( v11_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_409,plain,
    ( v2_lattice3(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_10])).

cnf(c_8,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_419,plain,
    ( v2_lattice3(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_409,c_8])).

cnf(c_473,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | g1_orders_2(k9_setfam_1(X2),k1_yellow_1(k9_setfam_1(X2))) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_419])).

cnf(c_474,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0),u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v4_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v5_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v1_lattice3(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v11_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_2,plain,
    ( v1_lattice3(X0)
    | v2_struct_0(X0)
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_384,plain,
    ( v1_lattice3(X0)
    | ~ v11_waybel_1(X0)
    | ~ l1_orders_2(X0)
    | g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_16])).

cnf(c_385,plain,
    ( v1_lattice3(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ v11_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_389,plain,
    ( v1_lattice3(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_10])).

cnf(c_399,plain,
    ( v1_lattice3(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_389,c_8])).

cnf(c_12,plain,
    ( v5_orders_2(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_13,plain,
    ( v4_orders_2(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_14,plain,
    ( v3_orders_2(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_502,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0),u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))))
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_474,c_8,c_10,c_399,c_12,c_13,c_14])).

cnf(c_667,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0),u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))))
    | v1_xboole_0(X0)
    | g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_502])).

cnf(c_668,plain,
    ( ~ v2_waybel_0(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2),u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | v1_xboole_0(sK2)
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(unflattening,[status(thm)],[c_667])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_672,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2),u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ v2_waybel_0(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_668,c_32])).

cnf(c_673,plain,
    ( ~ v2_waybel_0(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2),u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(renaming,[status(thm)],[c_672])).

cnf(c_779,plain,
    ( v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2),u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_673])).

cnf(c_1354,plain,
    ( v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2),u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_779])).

cnf(c_2256,plain,
    ( g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) = iProver_top
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2),u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))) = iProver_top
    | m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1354])).

cnf(c_3007,plain,
    ( v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2),u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))))) = iProver_top
    | m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2256])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3158,plain,
    ( m1_subset_1(sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2),u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))))) = iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3007,c_36])).

cnf(c_3159,plain,
    ( v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2),u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3158])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))))
    | k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0) = k6_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2264,plain,
    ( k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),X1) = k6_subset_1(X0,X1)
    | m1_subset_1(X1,u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3413,plain,
    ( k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)) = k6_subset_1(sK1,sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2))
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3159,c_2264])).

cnf(c_27,negated_conjecture,
    ( ~ v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))))
    | m1_subset_1(sK3,k9_setfam_1(sK1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2261,plain,
    ( v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) != iProver_top
    | m1_subset_1(sK3,k9_setfam_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3420,plain,
    ( k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)) = k6_subset_1(sK1,sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2))
    | m1_subset_1(sK3,k9_setfam_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3413,c_2261])).

cnf(c_2269,plain,
    ( l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | ~ v1_orders_2(X0)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2271,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
    | l1_orders_2(X0) != iProver_top
    | v1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2883,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0))
    | v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2269,c_2271])).

cnf(c_9,plain,
    ( v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_361,plain,
    ( ~ l1_orders_2(X0)
    | g1_orders_2(X1,k1_yellow_1(X1)) != X0
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_362,plain,
    ( ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
    | g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_3731,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))),u1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2883,c_8,c_362])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2265,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k9_setfam_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3734,plain,
    ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
    | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1
    | m1_subset_1(X2,k9_setfam_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3731,c_2265])).

cnf(c_3869,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0
    | m1_subset_1(k1_yellow_1(X0),k9_setfam_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3734])).

cnf(c_7,plain,
    ( m1_subset_1(k1_yellow_1(X0),k9_setfam_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_90,plain,
    ( m1_subset_1(k1_yellow_1(X0),k9_setfam_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3887,plain,
    ( u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3869,c_90])).

cnf(c_3891,plain,
    ( k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),X1) = k6_subset_1(X0,X1)
    | m1_subset_1(X1,k9_setfam_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3887,c_2264])).

cnf(c_4163,plain,
    ( k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)) = k6_subset_1(sK1,sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2))
    | k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK3) = k6_subset_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_3420,c_3891])).

cnf(c_19,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r2_hidden(k7_waybel_1(X1,sK0(X1,X0)),X0)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v11_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_550,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r2_hidden(k7_waybel_1(X1,sK0(X1,X0)),X0)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | g1_orders_2(k9_setfam_1(X2),k1_yellow_1(k9_setfam_1(X2))) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_419])).

cnf(c_551,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),sK0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0)),X0)
    | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v4_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v5_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v1_lattice3(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v11_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_579,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),sK0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0)),X0)
    | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_551,c_8,c_10,c_399,c_12,c_13,c_14,c_23])).

cnf(c_625,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),sK0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0)),X0)
    | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_579])).

cnf(c_626,plain,
    ( ~ v2_waybel_0(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2)),sK2)
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_819,plain,
    ( ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2)),sK2)
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_626])).

cnf(c_1346,plain,
    ( ~ r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2)),sK2)
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_819])).

cnf(c_2258,plain,
    ( g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2)),sK2) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) = iProver_top
    | m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1346])).

cnf(c_3000,plain,
    ( r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)),sK2) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top
    | m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2258])).

cnf(c_820,plain,
    ( g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != sK2
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2)),sK2) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) = iProver_top
    | m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_822,plain,
    ( g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != sK2
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)),sK2) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top
    | m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_820])).

cnf(c_1916,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2432,plain,
    ( g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) = g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_2502,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1916])).

cnf(c_3091,plain,
    ( v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3000,c_36,c_822,c_2432,c_2502])).

cnf(c_3092,plain,
    ( r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)),sK2) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_3091])).

cnf(c_4343,plain,
    ( k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK3) = k6_subset_1(sK1,sK3)
    | r2_hidden(k6_subset_1(sK1,sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)),sK2) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4163,c_3092])).

cnf(c_4575,plain,
    ( k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK3) = k6_subset_1(sK1,sK3)
    | r2_hidden(sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2),sK2) = iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2),k9_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2260,c_4343])).

cnf(c_20,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v11_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_512,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r2_hidden(sK0(X1,X0),X0)
    | v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | g1_orders_2(k9_setfam_1(X2),k1_yellow_1(k9_setfam_1(X2))) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_419])).

cnf(c_513,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ r2_hidden(sK0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0),X0)
    | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v4_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v5_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v1_lattice3(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v11_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_541,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ r2_hidden(sK0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0),X0)
    | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_513,c_8,c_10,c_399,c_12,c_13,c_14,c_23])).

cnf(c_646,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ r2_hidden(sK0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0),X0)
    | v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_541])).

cnf(c_647,plain,
    ( ~ v2_waybel_0(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ r2_hidden(sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2),sK2)
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_799,plain,
    ( ~ r2_hidden(sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2),sK2)
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_647])).

cnf(c_800,plain,
    ( g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != sK2
    | r2_hidden(sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2),sK2) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) = iProver_top
    | m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_802,plain,
    ( g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != sK2
    | r2_hidden(sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2),sK2) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top
    | m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_3892,plain,
    ( g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) = iProver_top
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),sK2),k9_setfam_1(X0)) = iProver_top
    | m1_subset_1(sK2,k9_setfam_1(k9_setfam_1(X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3887,c_2256])).

cnf(c_3967,plain,
    ( g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2),k9_setfam_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k9_setfam_1(k9_setfam_1(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3892])).

cnf(c_2259,plain,
    ( m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3898,plain,
    ( m1_subset_1(sK2,k9_setfam_1(k9_setfam_1(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3887,c_2259])).

cnf(c_4586,plain,
    ( v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top
    | k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK3) = k6_subset_1(sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4575,c_36,c_802,c_2432,c_2502,c_3897])).

cnf(c_4587,plain,
    ( k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK3) = k6_subset_1(sK1,sK3)
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4586])).

cnf(c_4594,plain,
    ( k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK3) = k6_subset_1(sK1,sK3)
    | m1_subset_1(sK3,k9_setfam_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4587,c_2261])).

cnf(c_4945,plain,
    ( k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK3) = k6_subset_1(sK1,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4594,c_3891])).

cnf(c_22,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | r2_hidden(X2,X0)
    | r2_hidden(k7_waybel_1(X1,X2),X0)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v11_waybel_1(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_428,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | r2_hidden(X2,X0)
    | r2_hidden(k7_waybel_1(X1,X2),X0)
    | ~ v2_waybel_7(X0,X1)
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1)
    | g1_orders_2(k9_setfam_1(X3),k1_yellow_1(k9_setfam_1(X3))) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_419])).

cnf(c_429,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | r2_hidden(X2,X0)
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X2),X0)
    | ~ v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v4_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v5_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v1_lattice3(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v11_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ l1_orders_2(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_461,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ v13_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | r2_hidden(X2,X0)
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X2),X0)
    | ~ v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))))
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_429,c_8,c_10,c_399,c_12,c_13,c_14])).

cnf(c_694,plain,
    ( ~ v2_waybel_0(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | r2_hidden(X2,X0)
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X2),X0)
    | ~ v2_waybel_7(X0,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))))
    | v1_xboole_0(X0)
    | g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_461])).

cnf(c_695,plain,
    ( ~ v2_waybel_0(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | r2_hidden(X1,sK2)
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),X1),sK2)
    | ~ v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | v1_xboole_0(sK2)
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(unflattening,[status(thm)],[c_694])).

cnf(c_699,plain,
    ( ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))
    | ~ v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),X1),sK2)
    | r2_hidden(X1,sK2)
    | ~ v2_waybel_0(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_695,c_32])).

cnf(c_700,plain,
    ( ~ v2_waybel_0(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | r2_hidden(X1,sK2)
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),X1),sK2)
    | ~ v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))))
    | g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(renaming,[status(thm)],[c_699])).

cnf(c_753,plain,
    ( r2_hidden(X0,sK2)
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0),sK2)
    | ~ v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_700])).

cnf(c_1358,plain,
    ( r2_hidden(X0,sK2)
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))),X0),sK2)
    | ~ v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))
    | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1)))))
    | ~ m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))))))
    | g1_orders_2(k9_setfam_1(X1),k1_yellow_1(k9_setfam_1(X1))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))) ),
    inference(equality_resolution_simp,[status(thm)],[c_753])).

cnf(c_2255,plain,
    ( g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))) != g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))
    | r2_hidden(X1,sK2) = iProver_top
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))),X1),sK2) = iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0))))) != iProver_top
    | m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(X0),k1_yellow_1(k9_setfam_1(X0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1358])).

cnf(c_2649,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),X0),sK2) = iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))))) != iProver_top
    | m1_subset_1(sK2,k9_setfam_1(u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2255])).

cnf(c_3165,plain,
    ( m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))))) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) != iProver_top
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),X0),sK2) = iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2649,c_36])).

cnf(c_3166,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),X0),sK2) = iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3165])).

cnf(c_3896,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),X0),sK2) = iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3887,c_3166])).

cnf(c_5565,plain,
    ( r2_hidden(k6_subset_1(sK1,sK3),sK2) = iProver_top
    | r2_hidden(sK3,sK2) = iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) != iProver_top
    | m1_subset_1(sK3,k9_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4945,c_3896])).

cnf(c_40,plain,
    ( v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) != iProver_top
    | m1_subset_1(sK3,k9_setfam_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(sK3,sK2)
    | ~ v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_41,plain,
    ( r2_hidden(sK3,sK2) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(k6_subset_1(sK1,sK3),sK2)
    | ~ v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_42,plain,
    ( r2_hidden(k6_subset_1(sK1,sK3),sK2) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5792,plain,
    ( v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5565,c_40,c_41,c_42])).

cnf(c_5798,plain,
    ( r2_hidden(X0,sK2) = iProver_top
    | r2_hidden(k6_subset_1(sK1,X0),sK2) = iProver_top
    | m1_subset_1(X0,k9_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2260,c_5792])).

cnf(c_5797,plain,
    ( k7_waybel_1(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)) = k6_subset_1(sK1,sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)) ),
    inference(superposition,[status(thm)],[c_3413,c_5792])).

cnf(c_6065,plain,
    ( r2_hidden(k6_subset_1(sK1,sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)),sK2) != iProver_top
    | v2_waybel_7(sK2,g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5797,c_3092])).

cnf(c_6069,plain,
    ( r2_hidden(k6_subset_1(sK1,sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6065,c_40,c_41,c_42,c_5565])).

cnf(c_6074,plain,
    ( r2_hidden(sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2),sK2) = iProver_top
    | m1_subset_1(sK0(g1_orders_2(k9_setfam_1(sK1),k1_yellow_1(k9_setfam_1(sK1))),sK2),k9_setfam_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5798,c_6069])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6074,c_5792,c_3898,c_3967,c_2502,c_2432,c_802,c_36])).


%------------------------------------------------------------------------------
