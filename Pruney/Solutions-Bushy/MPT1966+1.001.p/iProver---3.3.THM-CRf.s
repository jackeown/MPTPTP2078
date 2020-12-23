%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1966+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:56 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_7720)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0))
        & ~ v1_xboole_0(X1) )
     => ( v2_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v1_finset_1(X2) )
           => ( r1_tarski(X2,X1)
             => r2_hidden(k8_setfam_1(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & ~ v1_xboole_0(X1) )
       => ( v2_waybel_0(X1,k3_yellow_1(X0))
        <=> ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v1_finset_1(X2) )
             => ( r1_tarski(X2,X1)
               => r2_hidden(k8_setfam_1(X0,X2),X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k8_setfam_1(X0,X2),X1)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X2) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k8_setfam_1(X0,X2),X1)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X2) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f47])).

fof(f54,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k8_setfam_1(X0,X2),X1)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v1_finset_1(X2) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2] :
            ( r2_hidden(k8_setfam_1(X0,X2),X1)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X2) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f55,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k8_setfam_1(X0,X2),X1)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v1_finset_1(X2) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2] :
            ( r2_hidden(k8_setfam_1(X0,X2),X1)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X2) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f54])).

fof(f56,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k8_setfam_1(X0,X2),X1)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v1_finset_1(X2) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X3] :
            ( r2_hidden(k8_setfam_1(X0,X3),X1)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X3) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(rectify,[],[f55])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k8_setfam_1(X0,X2),X1)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v1_finset_1(X2) )
     => ( ~ r2_hidden(k8_setfam_1(X0,sK3),X1)
        & r1_tarski(sK3,X1)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(X0)))
        & v1_finset_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0,X1] :
        ( ( ? [X2] :
              ( ~ r2_hidden(k8_setfam_1(X0,X2),X1)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v1_finset_1(X2) )
          | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
        & ( ! [X3] :
              ( r2_hidden(k8_setfam_1(X0,X3),X1)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X0)))
              | ~ v1_finset_1(X3) )
          | v2_waybel_0(X1,k3_yellow_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0))
        & ~ v1_xboole_0(X1) )
   => ( ( ? [X2] :
            ( ~ r2_hidden(k8_setfam_1(sK1,X2),sK2)
            & r1_tarski(X2,sK2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
            & v1_finset_1(X2) )
        | ~ v2_waybel_0(sK2,k3_yellow_1(sK1)) )
      & ( ! [X3] :
            ( r2_hidden(k8_setfam_1(sK1,X3),sK2)
            | ~ r1_tarski(X3,sK2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
            | ~ v1_finset_1(X3) )
        | v2_waybel_0(sK2,k3_yellow_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK1))))
      & v13_waybel_0(sK2,k3_yellow_1(sK1))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ( ~ r2_hidden(k8_setfam_1(sK1,sK3),sK2)
        & r1_tarski(sK3,sK2)
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
        & v1_finset_1(sK3) )
      | ~ v2_waybel_0(sK2,k3_yellow_1(sK1)) )
    & ( ! [X3] :
          ( r2_hidden(k8_setfam_1(sK1,X3),sK2)
          | ~ r1_tarski(X3,sK2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
          | ~ v1_finset_1(X3) )
      | v2_waybel_0(sK2,k3_yellow_1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK1))))
    & v13_waybel_0(sK2,k3_yellow_1(sK1))
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f56,f58,f57])).

fof(f95,plain,(
    v13_waybel_0(sK2,k3_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f71,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ( k1_xboole_0 != X2
                 => r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f43])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) ) )
            & ( ! [X2] :
                  ( r2_hidden(k2_yellow_0(X0,X2),X1)
                  | k1_xboole_0 = X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X2) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) ) )
            & ( ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X1)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ~ r2_hidden(k2_yellow_0(X0,sK0(X0,X1)),X1)
        & k1_xboole_0 != sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK0(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ( ~ r2_hidden(k2_yellow_0(X0,sK0(X0,X1)),X1)
                & k1_xboole_0 != sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(X1))
                & v1_finset_1(sK0(X0,X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X1)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f51,f52])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f17,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(definition_unfolding,[],[f79,f91])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | m1_subset_1(sK0(X0,X1),u1_struct_0(k3_yellow_1(X1)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f88,f102,f102])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(pure_predicate_removal,[],[f25])).

fof(f27,plain,(
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
    inference(pure_predicate_removal,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f73,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f74,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f117,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) ),
    inference(definition_unfolding,[],[f96,f102])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) ) ),
    inference(definition_unfolding,[],[f84,f102])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f102])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) ) ),
    inference(definition_unfolding,[],[f69,f102,f102])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | k1_xboole_0 != sK0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | k1_xboole_0 != sK0(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f89,f102])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & ~ v1_xboole_0(X1) )
     => k1_setfam_1(X1) = k2_yellow_0(k3_yellow_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k2_yellow_0(k3_yellow_1(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k2_yellow_0(k3_yellow_1(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k2_yellow_0(k3_yellow_1(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k2_yellow_0(k3_yellow_1(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
      | v1_xboole_0(X1) ) ),
    inference(definition_unfolding,[],[f82,f102])).

fof(f6,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f92,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f99,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ v2_waybel_0(sK2,k3_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f115,plain,
    ( m1_subset_1(sK3,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1)))))
    | ~ v2_waybel_0(sK2,k3_yellow_1(sK1)) ),
    inference(definition_unfolding,[],[f99,f102,f102])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | ~ r2_hidden(k2_yellow_0(X0,sK0(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | ~ r2_hidden(k2_yellow_0(X0,sK0(X0,X1)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f90,f102])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | v1_finset_1(sK0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | v1_finset_1(sK0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f87,f102])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) ) ),
    inference(definition_unfolding,[],[f78,f102,f102])).

fof(f97,plain,(
    ! [X3] :
      ( r2_hidden(k8_setfam_1(sK1,X3),sK2)
      | ~ r1_tarski(X3,sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ v1_finset_1(X3)
      | v2_waybel_0(sK2,k3_yellow_1(sK1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f116,plain,(
    ! [X3] :
      ( r2_hidden(k8_setfam_1(sK1,X3),sK2)
      | ~ r1_tarski(X3,sK2)
      | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1)))))
      | ~ v1_finset_1(X3)
      | v2_waybel_0(sK2,k3_yellow_1(sK1)) ) ),
    inference(definition_unfolding,[],[f97,f102,f102])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k2_yellow_0(X0,X3),X1)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
      | ~ v1_finset_1(X3)
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k2_yellow_0(X0,X3),X1)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,u1_struct_0(k3_yellow_1(X1)))
      | ~ v1_finset_1(X3)
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_unfolding,[],[f86,f102,f102])).

fof(f101,plain,
    ( ~ r2_hidden(k8_setfam_1(sK1,sK3),sK2)
    | ~ v2_waybel_0(sK2,k3_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f100,plain,
    ( r1_tarski(sK3,sK2)
    | ~ v2_waybel_0(sK2,k3_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f98,plain,
    ( v1_finset_1(sK3)
    | ~ v2_waybel_0(sK2,k3_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) ) ),
    inference(definition_unfolding,[],[f70,f102,f102])).

fof(f118,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) ) ),
    inference(equality_resolution,[],[f103])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_waybel_1(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v9_waybel_1(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v9_waybel_1(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X0] :
      ( v9_waybel_1(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v9_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_yellow_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v9_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v9_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v9_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => r2_hidden(k4_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f83,f102])).

fof(f67,plain,(
    ! [X0] :
      ( v5_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X0] :
      ( v4_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X0] :
      ( v3_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

cnf(c_38,negated_conjecture,
    ( v13_waybel_0(sK2,k3_yellow_1(sK1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_11,plain,
    ( l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,plain,
    ( v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(k3_yellow_1(X0)))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_692,plain,
    ( v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X0),u1_struct_0(k3_yellow_1(X0)))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k3_yellow_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_693,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | m1_subset_1(sK0(k3_yellow_1(X1),X0),u1_struct_0(k3_yellow_1(X0)))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(k3_yellow_1(X1))
    | ~ v4_orders_2(k3_yellow_1(X1))
    | ~ v5_orders_2(k3_yellow_1(X1))
    | ~ v2_lattice3(k3_yellow_1(X1)) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_4,plain,
    ( v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v11_waybel_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
    ( v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_568,plain,
    ( v2_lattice3(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_569,plain,
    ( v2_lattice3(k3_yellow_1(X0))
    | ~ l1_orders_2(k3_yellow_1(X0))
    | v2_struct_0(k3_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_17,plain,
    ( ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_573,plain,
    ( v2_lattice3(k3_yellow_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_17,c_11])).

cnf(c_14,plain,
    ( v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_15,plain,
    ( v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_16,plain,
    ( v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_715,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | m1_subset_1(sK0(k3_yellow_1(X1),X0),u1_struct_0(k3_yellow_1(X0)))
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_693,c_573,c_14,c_15,c_16])).

cnf(c_869,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | m1_subset_1(sK0(k3_yellow_1(X1),X0),u1_struct_0(k3_yellow_1(X0)))
    | v1_xboole_0(X0)
    | k3_yellow_1(X1) != k3_yellow_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_715])).

cnf(c_870,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(X0))
    | m1_subset_1(sK0(k3_yellow_1(X0),sK2),u1_struct_0(k3_yellow_1(sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | v1_xboole_0(sK2)
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(unflattening,[status(thm)],[c_869])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_874,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | m1_subset_1(sK0(k3_yellow_1(X0),sK2),u1_struct_0(k3_yellow_1(sK2)))
    | v2_waybel_0(sK2,k3_yellow_1(X0))
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_870,c_39])).

cnf(c_875,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(X0))
    | m1_subset_1(sK0(k3_yellow_1(X0),sK2),u1_struct_0(k3_yellow_1(sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(renaming,[status(thm)],[c_874])).

cnf(c_3913,plain,
    ( k3_yellow_1(X0) != k3_yellow_1(sK1)
    | v2_waybel_0(sK2,k3_yellow_1(X0)) = iProver_top
    | m1_subset_1(sK0(k3_yellow_1(X0),sK2),u1_struct_0(k3_yellow_1(sK2))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_4616,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | m1_subset_1(sK0(k3_yellow_1(sK1),sK2),u1_struct_0(k3_yellow_1(sK2))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3913])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5096,plain,
    ( m1_subset_1(sK0(k3_yellow_1(sK1),sK2),u1_struct_0(k3_yellow_1(sK2))) = iProver_top
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4616,c_42])).

cnf(c_5097,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | m1_subset_1(sK0(k3_yellow_1(sK1),sK2),u1_struct_0(k3_yellow_1(sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_5096])).

cnf(c_24,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_3925,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5102,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r1_tarski(sK0(k3_yellow_1(sK1),sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5097,c_3925])).

cnf(c_3917,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4351,plain,
    ( r1_tarski(sK2,u1_struct_0(k3_yellow_1(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3917,c_3925])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3928,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4818,plain,
    ( r1_tarski(X0,u1_struct_0(k3_yellow_1(sK1))) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4351,c_3928])).

cnf(c_23,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3926,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3931,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5235,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | r1_tarski(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3926,c_3931])).

cnf(c_5911,plain,
    ( k6_setfam_1(sK1,X0) = k8_setfam_1(sK1,X0)
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4818,c_5235])).

cnf(c_6417,plain,
    ( sK0(k3_yellow_1(sK1),sK2) = k1_xboole_0
    | k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5102,c_5911])).

cnf(c_3317,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4151,plain,
    ( k3_yellow_1(sK1) = k3_yellow_1(sK1) ),
    inference(instantiation,[status(thm)],[c_3317])).

cnf(c_26,plain,
    ( v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | sK0(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_724,plain,
    ( v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | sK0(X1,X0) != k1_xboole_0
    | k3_yellow_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_725,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(k3_yellow_1(X1))
    | ~ v4_orders_2(k3_yellow_1(X1))
    | ~ v5_orders_2(k3_yellow_1(X1))
    | ~ v2_lattice3(k3_yellow_1(X1))
    | sK0(k3_yellow_1(X1),X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_724])).

cnf(c_747,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_xboole_0(X0)
    | sK0(k3_yellow_1(X1),X0) != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_725,c_573,c_14,c_15,c_16])).

cnf(c_845,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_xboole_0(X0)
    | sK0(k3_yellow_1(X1),X0) != k1_xboole_0
    | k3_yellow_1(X1) != k3_yellow_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_747])).

cnf(c_846,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(X0))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | v1_xboole_0(sK2)
    | sK0(k3_yellow_1(X0),sK2) != k1_xboole_0
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(unflattening,[status(thm)],[c_845])).

cnf(c_850,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | v2_waybel_0(sK2,k3_yellow_1(X0))
    | sK0(k3_yellow_1(X0),sK2) != k1_xboole_0
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_846,c_39])).

cnf(c_851,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(X0))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | sK0(k3_yellow_1(X0),sK2) != k1_xboole_0
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(renaming,[status(thm)],[c_850])).

cnf(c_4155,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1)))))
    | sK0(k3_yellow_1(sK1),sK2) != k1_xboole_0
    | k3_yellow_1(sK1) != k3_yellow_1(sK1) ),
    inference(instantiation,[status(thm)],[c_851])).

cnf(c_4156,plain,
    ( sK0(k3_yellow_1(sK1),sK2) != k1_xboole_0
    | k3_yellow_1(sK1) != k3_yellow_1(sK1)
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4155])).

cnf(c_7596,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6417,c_42,c_4151,c_4156])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_xboole_0(X0)
    | k2_yellow_0(k3_yellow_1(X1),X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3927,plain,
    ( k2_yellow_0(k3_yellow_1(X0),X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5108,plain,
    ( k2_yellow_0(k3_yellow_1(X0),X1) = k1_setfam_1(X1)
    | r1_tarski(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3926,c_3927])).

cnf(c_6298,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),X0) = k1_setfam_1(X0)
    | r1_tarski(X0,sK2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4818,c_5108])).

cnf(c_6479,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | v1_xboole_0(sK0(k3_yellow_1(sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5102,c_6298])).

cnf(c_12,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_99,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_30,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4124,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3323,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4143,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3323])).

cnf(c_4310,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4143])).

cnf(c_4311,plain,
    ( k1_xboole_0 != o_0_0_xboole_0
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4310])).

cnf(c_31,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_4417,plain,
    ( ~ v1_xboole_0(sK0(k3_yellow_1(sK1),sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0(k3_yellow_1(sK1),sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_4418,plain,
    ( sK0(k3_yellow_1(sK1),sK2) = k1_xboole_0
    | v1_xboole_0(sK0(k3_yellow_1(sK1),sK2)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4417])).

cnf(c_7706,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6479,c_42,c_12,c_99,c_4124,c_4151,c_4156,c_4311,c_4418])).

cnf(c_7707,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7706])).

cnf(c_34,negated_conjecture,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(sK1))
    | m1_subset_1(sK3,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3920,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5109,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3920,c_3927])).

cnf(c_7717,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7707,c_5109])).

cnf(c_3924,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8214,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7717,c_3924])).

cnf(c_25,plain,
    ( v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r2_hidden(k2_yellow_0(X1,sK0(X1,X0)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_756,plain,
    ( v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ r2_hidden(k2_yellow_0(X1,sK0(X1,X0)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k3_yellow_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_757,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ r2_hidden(k2_yellow_0(k3_yellow_1(X1),sK0(k3_yellow_1(X1),X0)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(k3_yellow_1(X1))
    | ~ v4_orders_2(k3_yellow_1(X1))
    | ~ v5_orders_2(k3_yellow_1(X1))
    | ~ v2_lattice3(k3_yellow_1(X1)) ),
    inference(unflattening,[status(thm)],[c_756])).

cnf(c_779,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ r2_hidden(k2_yellow_0(k3_yellow_1(X1),sK0(k3_yellow_1(X1),X0)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_757,c_573,c_14,c_15,c_16])).

cnf(c_821,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ r2_hidden(k2_yellow_0(k3_yellow_1(X1),sK0(k3_yellow_1(X1),X0)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_xboole_0(X0)
    | k3_yellow_1(X1) != k3_yellow_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_779])).

cnf(c_822,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(X0))
    | ~ r2_hidden(k2_yellow_0(k3_yellow_1(X0),sK0(k3_yellow_1(X0),sK2)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | v1_xboole_0(sK2)
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_826,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | ~ r2_hidden(k2_yellow_0(k3_yellow_1(X0),sK0(k3_yellow_1(X0),sK2)),sK2)
    | v2_waybel_0(sK2,k3_yellow_1(X0))
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_822,c_39])).

cnf(c_827,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(X0))
    | ~ r2_hidden(k2_yellow_0(k3_yellow_1(X0),sK0(k3_yellow_1(X0),sK2)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(renaming,[status(thm)],[c_826])).

cnf(c_3915,plain,
    ( k3_yellow_1(X0) != k3_yellow_1(sK1)
    | v2_waybel_0(sK2,k3_yellow_1(X0)) = iProver_top
    | r2_hidden(k2_yellow_0(k3_yellow_1(X0),sK0(k3_yellow_1(X0),sK2)),sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_4478,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)),sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3915])).

cnf(c_4947,plain,
    ( r2_hidden(k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)),sK2) != iProver_top
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4478,c_42])).

cnf(c_4948,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)),sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4947])).

cnf(c_8510,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_4948])).

cnf(c_28,plain,
    ( v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v1_finset_1(sK0(X1,X0))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_660,plain,
    ( v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v1_finset_1(sK0(X1,X0))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k3_yellow_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_661,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_finset_1(sK0(k3_yellow_1(X1),X0))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(k3_yellow_1(X1))
    | ~ v4_orders_2(k3_yellow_1(X1))
    | ~ v5_orders_2(k3_yellow_1(X1))
    | ~ v2_lattice3(k3_yellow_1(X1)) ),
    inference(unflattening,[status(thm)],[c_660])).

cnf(c_683,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_finset_1(sK0(k3_yellow_1(X1),X0))
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_661,c_573,c_14,c_15,c_16])).

cnf(c_893,plain,
    ( v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_finset_1(sK0(k3_yellow_1(X1),X0))
    | v1_xboole_0(X0)
    | k3_yellow_1(X1) != k3_yellow_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_683])).

cnf(c_894,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(X0))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | v1_finset_1(sK0(k3_yellow_1(X0),sK2))
    | v1_xboole_0(sK2)
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(unflattening,[status(thm)],[c_893])).

cnf(c_898,plain,
    ( v1_finset_1(sK0(k3_yellow_1(X0),sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | v2_waybel_0(sK2,k3_yellow_1(X0))
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_894,c_39])).

cnf(c_899,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(X0))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | v1_finset_1(sK0(k3_yellow_1(X0),sK2))
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(renaming,[status(thm)],[c_898])).

cnf(c_4153,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1)))))
    | v1_finset_1(sK0(k3_yellow_1(sK1),sK2))
    | k3_yellow_1(sK1) != k3_yellow_1(sK1) ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_4160,plain,
    ( k3_yellow_1(sK1) != k3_yellow_1(sK1)
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) != iProver_top
    | v1_finset_1(sK0(k3_yellow_1(sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4153])).

cnf(c_7607,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7596,c_5109])).

cnf(c_8192,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7607,c_3924])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3929,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4745,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | r1_tarski(X1,u1_struct_0(k3_yellow_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3926,c_3929])).

cnf(c_5810,plain,
    ( k6_setfam_1(sK1,X0) = k1_setfam_1(X0)
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4818,c_4745])).

cnf(c_6102,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5102,c_5810])).

cnf(c_6590,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6102,c_5109])).

cnf(c_7185,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6590,c_3924])).

cnf(c_8479,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8192,c_7185])).

cnf(c_36,negated_conjecture,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1))
    | r2_hidden(k8_setfam_1(sK1,X0),sK2)
    | ~ r1_tarski(X0,sK2)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1)))))
    | ~ v1_finset_1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3918,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k8_setfam_1(sK1,X0),sK2) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) != iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4403,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k8_setfam_1(sK1,X0),sK2) = iProver_top
    | r1_tarski(X0,u1_struct_0(k3_yellow_1(sK1))) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3926,c_3918])).

cnf(c_4127,plain,
    ( r1_tarski(sK2,u1_struct_0(k3_yellow_1(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_4128,plain,
    ( r1_tarski(sK2,u1_struct_0(k3_yellow_1(sK1))) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4127])).

cnf(c_4184,plain,
    ( r1_tarski(X0,u1_struct_0(k3_yellow_1(sK1)))
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(k3_yellow_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_4186,plain,
    ( r1_tarski(X0,u1_struct_0(k3_yellow_1(sK1))) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,u1_struct_0(k3_yellow_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4184])).

cnf(c_4619,plain,
    ( r2_hidden(k8_setfam_1(sK1,X0),sK2) = iProver_top
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4403,c_42,c_4128,c_4186])).

cnf(c_4620,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k8_setfam_1(sK1,X0),sK2) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4619])).

cnf(c_9725,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) = iProver_top
    | r1_tarski(sK0(k3_yellow_1(sK1),sK2),sK2) != iProver_top
    | v1_finset_1(sK0(k3_yellow_1(sK1),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8479,c_4620])).

cnf(c_9994,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | sK3 = k1_xboole_0
    | k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8510,c_42,c_4151,c_4160,c_5102,c_9725])).

cnf(c_9995,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9994])).

cnf(c_10007,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_9995,c_5109])).

cnf(c_10284,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10007,c_3924])).

cnf(c_29,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | r2_hidden(k2_yellow_0(X1,X2),X0)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v1_finset_1(X2)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_619,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | r2_hidden(k2_yellow_0(X1,X2),X0)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | ~ v1_finset_1(X2)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | k3_yellow_1(X3) != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_620,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | r2_hidden(k2_yellow_0(k3_yellow_1(X1),X2),X0)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | ~ v1_finset_1(X2)
    | v1_xboole_0(X0)
    | ~ v3_orders_2(k3_yellow_1(X1))
    | ~ v4_orders_2(k3_yellow_1(X1))
    | ~ v5_orders_2(k3_yellow_1(X1))
    | ~ v2_lattice3(k3_yellow_1(X1))
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_648,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | r2_hidden(k2_yellow_0(k3_yellow_1(X1),X2),X0)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | ~ v1_finset_1(X2)
    | v1_xboole_0(X0)
    | k1_xboole_0 = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_620,c_573,c_14,c_15,c_16])).

cnf(c_917,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | r2_hidden(k2_yellow_0(k3_yellow_1(X1),X2),X0)
    | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | ~ v1_finset_1(X2)
    | v1_xboole_0(X0)
    | k3_yellow_1(X1) != k3_yellow_1(sK1)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_648])).

cnf(c_918,plain,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(X0))
    | r2_hidden(k2_yellow_0(k3_yellow_1(X0),X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | ~ v1_finset_1(X1)
    | v1_xboole_0(sK2)
    | k3_yellow_1(X0) != k3_yellow_1(sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_917])).

cnf(c_922,plain,
    ( ~ v1_finset_1(X1)
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK2)))
    | r2_hidden(k2_yellow_0(k3_yellow_1(X0),X1),sK2)
    | ~ v2_waybel_0(sK2,k3_yellow_1(X0))
    | k3_yellow_1(X0) != k3_yellow_1(sK1)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_918,c_39])).

cnf(c_923,plain,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(X0))
    | r2_hidden(k2_yellow_0(k3_yellow_1(X0),X1),sK2)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | ~ v1_finset_1(X1)
    | k3_yellow_1(X0) != k3_yellow_1(sK1)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_922])).

cnf(c_3911,plain,
    ( k3_yellow_1(X0) != k3_yellow_1(sK1)
    | k1_xboole_0 = X1
    | v2_waybel_0(sK2,k3_yellow_1(X0)) != iProver_top
    | r2_hidden(k2_yellow_0(k3_yellow_1(X0),X1),sK2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k3_yellow_1(sK2))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) != iProver_top
    | v1_finset_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_923])).

cnf(c_4658,plain,
    ( k1_xboole_0 = X0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | r2_hidden(k2_yellow_0(k3_yellow_1(sK1),X0),sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK2))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) != iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3911])).

cnf(c_5694,plain,
    ( m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK2))) != iProver_top
    | r2_hidden(k2_yellow_0(k3_yellow_1(sK1),X0),sK2) = iProver_top
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | k1_xboole_0 = X0
    | v1_finset_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4658,c_42])).

cnf(c_5695,plain,
    ( k1_xboole_0 = X0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | r2_hidden(k2_yellow_0(k3_yellow_1(sK1),X0),sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK2))) != iProver_top
    | v1_finset_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5694])).

cnf(c_10375,plain,
    ( sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | r2_hidden(k1_setfam_1(sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK2))) != iProver_top
    | v1_finset_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10284,c_5695])).

cnf(c_4335,plain,
    ( r1_tarski(sK3,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_4336,plain,
    ( r1_tarski(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4335])).

cnf(c_4746,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3920,c_3929])).

cnf(c_7609,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_7596,c_4746])).

cnf(c_6592,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_6102,c_4746])).

cnf(c_8044,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_7609,c_6592])).

cnf(c_8727,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) = iProver_top
    | r1_tarski(sK0(k3_yellow_1(sK1),sK2),sK2) != iProver_top
    | v1_finset_1(sK0(k3_yellow_1(sK1),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8044,c_4620])).

cnf(c_7719,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_7707,c_4746])).

cnf(c_8051,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7719,c_4948])).

cnf(c_8730,plain,
    ( k6_setfam_1(sK1,sK3) = k1_setfam_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8727,c_42,c_4151,c_4160,c_4746,c_5102,c_8051])).

cnf(c_5236,plain,
    ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3920,c_3931])).

cnf(c_7608,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7596,c_5236])).

cnf(c_8734,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8730,c_7608])).

cnf(c_8736,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8730,c_5236])).

cnf(c_6591,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6102,c_5236])).

cnf(c_8108,plain,
    ( k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7608,c_6591])).

cnf(c_8848,plain,
    ( k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8108,c_8730])).

cnf(c_8852,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) = iProver_top
    | r1_tarski(sK0(k3_yellow_1(sK1),sK2),sK2) != iProver_top
    | v1_finset_1(sK0(k3_yellow_1(sK1),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8848,c_4620])).

cnf(c_8855,plain,
    ( sK3 = k1_xboole_0
    | k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8852,c_42,c_4151,c_4160,c_5102,c_8736])).

cnf(c_8856,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_8855])).

cnf(c_7718,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | k6_setfam_1(sK1,sK3) = k8_setfam_1(sK1,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7707,c_5236])).

cnf(c_8733,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8730,c_7718])).

cnf(c_9128,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8733,c_4948])).

cnf(c_9221,plain,
    ( k8_setfam_1(sK1,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8734,c_8736,c_8856,c_9128])).

cnf(c_9226,plain,
    ( sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK3),sK2) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top
    | v1_finset_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9221,c_4620])).

cnf(c_10494,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(k1_setfam_1(sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK2))) != iProver_top
    | v1_finset_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10375,c_4336,c_9226])).

cnf(c_10502,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(k1_setfam_1(sK3),sK2) = iProver_top
    | r1_tarski(sK3,sK2) != iProver_top
    | v1_finset_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3926,c_10494])).

cnf(c_32,negated_conjecture,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(sK1))
    | ~ r2_hidden(k8_setfam_1(sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3922,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | r2_hidden(k8_setfam_1(sK1,sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_9225,plain,
    ( sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | r2_hidden(k1_setfam_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9221,c_3922])).

cnf(c_9250,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0
    | r2_hidden(k1_setfam_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7596,c_9225])).

cnf(c_10509,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0
    | r1_tarski(sK3,sK2) != iProver_top
    | v1_finset_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10502,c_9250])).

cnf(c_33,negated_conjecture,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(sK1))
    | r1_tarski(sK3,sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3921,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7610,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7596,c_3921])).

cnf(c_35,negated_conjecture,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(sK1))
    | v1_finset_1(sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3919,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | v1_finset_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7611,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | v1_finset_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7596,c_3919])).

cnf(c_10597,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10509,c_7610,c_7611])).

cnf(c_9251,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0
    | r2_hidden(k1_setfam_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6102,c_9225])).

cnf(c_10511,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0
    | r1_tarski(sK3,sK2) != iProver_top
    | v1_finset_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10502,c_9251])).

cnf(c_6593,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6102,c_3921])).

cnf(c_6594,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | v1_finset_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6102,c_3919])).

cnf(c_10583,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10511,c_6593,c_6594])).

cnf(c_10605,plain,
    ( k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10597,c_10583])).

cnf(c_10951,plain,
    ( sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) = iProver_top
    | r1_tarski(sK0(k3_yellow_1(sK1),sK2),sK2) != iProver_top
    | v1_finset_1(sK0(k3_yellow_1(sK1),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10605,c_4620])).

cnf(c_9249,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0
    | r2_hidden(k1_setfam_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7707,c_9225])).

cnf(c_10510,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0
    | r1_tarski(sK3,sK2) != iProver_top
    | v1_finset_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10502,c_9249])).

cnf(c_46,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | v1_finset_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_48,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | r1_tarski(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10663,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10510,c_7720,c_7721])).

cnf(c_10667,plain,
    ( sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10663,c_4948])).

cnf(c_10690,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10667,c_46,c_48,c_9225,c_10502])).

cnf(c_8511,plain,
    ( sK0(k3_yellow_1(sK1),sK2) = k1_xboole_0
    | k2_yellow_0(k3_yellow_1(sK1),sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) = iProver_top
    | m1_subset_1(sK0(k3_yellow_1(sK1),sK2),u1_struct_0(k3_yellow_1(sK2))) != iProver_top
    | v1_finset_1(sK0(k3_yellow_1(sK1),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_5695])).

cnf(c_10822,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8511,c_46,c_48,c_9225,c_10502])).

cnf(c_10823,plain,
    ( sK3 = k1_xboole_0
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10822])).

cnf(c_11025,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10951,c_42,c_4151,c_4160,c_5102,c_10690,c_10823])).

cnf(c_11081,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | m1_subset_1(k1_xboole_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11025,c_3920])).

cnf(c_9,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_3932,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11540,plain,
    ( k8_setfam_1(sK1,k1_xboole_0) = sK1
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11081,c_3932])).

cnf(c_11555,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2))
    | k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_7596,c_11540])).

cnf(c_11556,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_6102,c_11540])).

cnf(c_13267,plain,
    ( k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_11555,c_11556])).

cnf(c_14160,plain,
    ( k8_setfam_1(sK1,k1_xboole_0) = sK1
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) = iProver_top
    | r1_tarski(sK0(k3_yellow_1(sK1),sK2),sK2) != iProver_top
    | v1_finset_1(sK0(k3_yellow_1(sK1),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13267,c_4620])).

cnf(c_11554,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2))
    | k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_7707,c_11540])).

cnf(c_13254,plain,
    ( k8_setfam_1(sK1,k1_xboole_0) = sK1
    | v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11554,c_4948])).

cnf(c_14189,plain,
    ( k8_setfam_1(sK1,k1_xboole_0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14160,c_42,c_4151,c_4160,c_5102,c_11540,c_13254])).

cnf(c_11082,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | r2_hidden(k8_setfam_1(sK1,k1_xboole_0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11025,c_3922])).

cnf(c_14192,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14189,c_11082])).

cnf(c_0,plain,
    ( ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v11_waybel_1(X0)
    | v9_waybel_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2,plain,
    ( v2_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v9_waybel_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_492,plain,
    ( v2_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v11_waybel_1(X0) ),
    inference(resolution,[status(thm)],[c_0,c_2])).

cnf(c_22,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_514,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_492,c_22])).

cnf(c_515,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v1_xboole_0(X0)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_5,plain,
    ( v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v11_waybel_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_6,plain,
    ( v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v11_waybel_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_7,plain,
    ( v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | ~ v11_waybel_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_541,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_515,c_5,c_6,c_7])).

cnf(c_583,plain,
    ( ~ v2_waybel_0(X0,X1)
    | ~ v13_waybel_0(X0,X1)
    | r2_hidden(k4_yellow_0(X1),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(X1))))
    | v1_xboole_0(X0)
    | ~ l1_orders_2(X1)
    | v2_struct_0(X1)
    | k3_yellow_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_541])).

cnf(c_584,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | r2_hidden(k4_yellow_0(k3_yellow_1(X1)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_xboole_0(X0)
    | ~ l1_orders_2(k3_yellow_1(X1))
    | v2_struct_0(k3_yellow_1(X1)) ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_602,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | ~ v13_waybel_0(X0,k3_yellow_1(X1))
    | r2_hidden(k4_yellow_0(k3_yellow_1(X1)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_xboole_0(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_584,c_17,c_11])).

cnf(c_950,plain,
    ( ~ v2_waybel_0(X0,k3_yellow_1(X1))
    | r2_hidden(k4_yellow_0(k3_yellow_1(X1)),X0)
    | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X1)))))
    | v1_xboole_0(X0)
    | k3_yellow_1(X1) != k3_yellow_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_602])).

cnf(c_951,plain,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(X0))
    | r2_hidden(k4_yellow_0(k3_yellow_1(X0)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | v1_xboole_0(sK2)
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(unflattening,[status(thm)],[c_950])).

cnf(c_955,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | r2_hidden(k4_yellow_0(k3_yellow_1(X0)),sK2)
    | ~ v2_waybel_0(sK2,k3_yellow_1(X0))
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_951,c_39])).

cnf(c_956,plain,
    ( ~ v2_waybel_0(sK2,k3_yellow_1(X0))
    | r2_hidden(k4_yellow_0(k3_yellow_1(X0)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
    | k3_yellow_1(X0) != k3_yellow_1(sK1) ),
    inference(renaming,[status(thm)],[c_955])).

cnf(c_3910,plain,
    ( k3_yellow_1(X0) != k3_yellow_1(sK1)
    | v2_waybel_0(sK2,k3_yellow_1(X0)) != iProver_top
    | r2_hidden(k4_yellow_0(k3_yellow_1(X0)),sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_19,plain,
    ( k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4017,plain,
    ( k3_yellow_1(X0) != k3_yellow_1(sK1)
    | v2_waybel_0(sK2,k3_yellow_1(X0)) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3910,c_19])).

cnf(c_5022,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top
    | r2_hidden(sK1,sK2) = iProver_top
    | m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK1))))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4017])).

cnf(c_14197,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14192,c_42,c_5022])).

cnf(c_14203,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_7596,c_14197])).

cnf(c_14204,plain,
    ( k6_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_6102,c_14197])).

cnf(c_14208,plain,
    ( k8_setfam_1(sK1,sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)) ),
    inference(light_normalisation,[status(thm)],[c_14203,c_14204])).

cnf(c_14467,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) = iProver_top
    | r1_tarski(sK0(k3_yellow_1(sK1),sK2),sK2) != iProver_top
    | v1_finset_1(sK0(k3_yellow_1(sK1),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14208,c_4620])).

cnf(c_14202,plain,
    ( k2_yellow_0(k3_yellow_1(sK1),sK0(k3_yellow_1(sK1),sK2)) = k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_7707,c_14197])).

cnf(c_14429,plain,
    ( v2_waybel_0(sK2,k3_yellow_1(sK1)) = iProver_top
    | r2_hidden(k1_setfam_1(sK0(k3_yellow_1(sK1),sK2)),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14202,c_4948])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14467,c_14429,c_14197,c_5102,c_4160,c_4151,c_42])).


%------------------------------------------------------------------------------
