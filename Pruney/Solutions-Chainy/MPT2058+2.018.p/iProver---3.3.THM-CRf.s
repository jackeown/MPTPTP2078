%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:18 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  215 (1994 expanded)
%              Number of clauses        :  138 ( 454 expanded)
%              Number of leaves         :   16 ( 544 expanded)
%              Depth                    :   33
%              Number of atoms          : 1385 (16766 expanded)
%              Number of equality atoms :  204 ( 535 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_waybel_7(X0,X1,X2)
            | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & ( r1_waybel_7(X0,X1,X2)
            | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_waybel_7(X0,X1,sK2)
          | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2) )
        & ( r1_waybel_7(X0,X1,sK2)
          | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(X0,X1,X2)
                | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & ( r1_waybel_7(X0,X1,X2)
                | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ( ~ r1_waybel_7(X0,sK1,X2)
              | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2) )
            & ( r1_waybel_7(X0,sK1,X2)
              | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_waybel_7(X0,X1,X2)
                  | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & ( r1_waybel_7(X0,X1,X2)
                  | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_waybel_7(sK0,X1,X2)
                | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
              & ( r1_waybel_7(sK0,X1,X2)
                | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ~ r1_waybel_7(sK0,sK1,sK2)
      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
    & ( r1_waybel_7(sK0,sK1,sK2)
      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42,f41,f40])).

fof(f66,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f81,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f66,f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f53,f49,f49,f49])).

fof(f71,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_waybel_9(X0,X1,X2)
                  | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r3_waybel_9(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r3_waybel_9(X0,X1,X2)
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f67,f49])).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f55,f49,f49,f49])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f52,f49,f49,f49])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f65,f49])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f60,f49,f49,f49,f49])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f68,f49])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f49,f49,f49,f49])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f70,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_21,negated_conjecture,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_7,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_16,negated_conjecture,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_199,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_391,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_392,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_396,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_26,c_24])).

cnf(c_673,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_199,c_396])).

cnf(c_674,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_676,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_18])).

cnf(c_677,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_676])).

cnf(c_713,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_677])).

cnf(c_714,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_713])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_73,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_718,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_714,c_26,c_24,c_73])).

cnf(c_719,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
    inference(renaming,[status(thm)],[c_718])).

cnf(c_20,negated_conjecture,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1403,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_719,c_20])).

cnf(c_1404,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1403])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1408,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1404,c_23])).

cnf(c_1409,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1408])).

cnf(c_1644,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1409])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_440,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_441,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_811,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_441])).

cnf(c_812,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_811])).

cnf(c_70,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_814,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_812,c_26,c_24,c_70,c_73])).

cnf(c_2526,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1644,c_814])).

cnf(c_2527,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2526])).

cnf(c_9,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_863,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_441])).

cnf(c_864,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_863])).

cnf(c_868,plain,
    ( v4_orders_2(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_864,c_26])).

cnf(c_869,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_868])).

cnf(c_1328,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_869,c_20])).

cnf(c_1329,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1328])).

cnf(c_1333,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1329,c_23])).

cnf(c_1334,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1333])).

cnf(c_1720,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1334])).

cnf(c_2479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1720,c_814])).

cnf(c_2480,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v4_orders_2(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2479])).

cnf(c_2792,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_2527,c_2480])).

cnf(c_8,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_896,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_441])).

cnf(c_897,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_896])).

cnf(c_901,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_897,c_26])).

cnf(c_902,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_901])).

cnf(c_1298,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_902,c_20])).

cnf(c_1299,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1298])).

cnf(c_1303,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1299,c_23])).

cnf(c_1304,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1303])).

cnf(c_1743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1304])).

cnf(c_2463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1743,c_814])).

cnf(c_2464,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v2_struct_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2463])).

cnf(c_3146,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_2792,c_2464])).

cnf(c_4245,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
    | r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3146])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_822,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_441])).

cnf(c_823,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_822])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_15,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_929,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_441])).

cnf(c_930,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_934,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_26])).

cnf(c_935,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 ),
    inference(renaming,[status(thm)],[c_934])).

cnf(c_1109,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_935])).

cnf(c_1110,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v1_xboole_0(sK1)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_1109])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1112,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1110,c_23,c_21,c_20,c_19])).

cnf(c_4342,plain,
    ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4245,c_823,c_1112])).

cnf(c_4343,plain,
    ( r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4342])).

cnf(c_5,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_827,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_441])).

cnf(c_828,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_waybel_0(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_827])).

cnf(c_832,plain,
    ( v7_waybel_0(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_828,c_26])).

cnf(c_833,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_waybel_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_832])).

cnf(c_1012,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_waybel_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X0 != X2
    | X3 = X2
    | u1_struct_0(k3_lattice3(k1_lattice3(X1))) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_833])).

cnf(c_1013,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_waybel_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(X1))) = X0 ),
    inference(unflattening,[status(thm)],[c_1012])).

cnf(c_1265,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v7_waybel_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | u1_struct_0(k3_lattice3(k1_lattice3(X1))) = X0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1013,c_20])).

cnf(c_1266,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK1 ),
    inference(unflattening,[status(thm)],[c_1265])).

cnf(c_1270,plain,
    ( v1_xboole_0(X0)
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1266,c_23])).

cnf(c_1271,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK1 ),
    inference(renaming,[status(thm)],[c_1270])).

cnf(c_1766,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1271])).

cnf(c_2444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK1
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1766,c_814])).

cnf(c_2445,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v7_waybel_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) = sK1 ),
    inference(unflattening,[status(thm)],[c_2444])).

cnf(c_4250,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) = sK1
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2445])).

cnf(c_4288,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) = sK1
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4250,c_823])).

cnf(c_4289,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) = sK1
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4288])).

cnf(c_4254,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_0,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4256,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_994,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | k2_subset_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_995,plain,
    ( ~ m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))
    | X0 = k2_subset_1(X0) ),
    inference(unflattening,[status(thm)],[c_994])).

cnf(c_999,plain,
    ( X0 = k2_subset_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_995,c_0])).

cnf(c_4264,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4256,c_999])).

cnf(c_1005,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != X0
    | k2_subset_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_1006,plain,
    ( k2_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) != sK1 ),
    inference(unflattening,[status(thm)],[c_1005])).

cnf(c_4269,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != sK1 ),
    inference(demodulation,[status(thm)],[c_1006,c_999])).

cnf(c_4294,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4289,c_4254,c_4264,c_4269])).

cnf(c_17,negated_conjecture,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_201,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_358,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_359,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_363,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_26,c_24])).

cnf(c_647,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_363])).

cnf(c_648,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_650,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,sK1,sK2)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_18])).

cnf(c_651,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_650])).

cnf(c_761,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_651])).

cnf(c_762,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_766,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_762,c_26,c_24,c_73])).

cnf(c_767,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
    inference(renaming,[status(thm)],[c_766])).

cnf(c_1358,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_767,c_20])).

cnf(c_1359,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1358])).

cnf(c_1363,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | r1_waybel_7(sK0,sK1,sK2)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1359,c_23])).

cnf(c_1364,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1363])).

cnf(c_1682,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1364])).

cnf(c_2495,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1682,c_814])).

cnf(c_2496,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2495])).

cnf(c_2819,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_2496,c_2480])).

cnf(c_3122,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_2819,c_2464])).

cnf(c_4246,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3122])).

cnf(c_4334,plain,
    ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4246,c_823,c_1112])).

cnf(c_4335,plain,
    ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4334])).

cnf(c_4340,plain,
    ( r1_waybel_7(sK0,sK1,sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4335,c_4294,c_4254,c_4264])).

cnf(c_4348,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4343,c_4294,c_4254,c_4264,c_4340])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:23:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.99/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/0.99  
% 1.99/0.99  ------  iProver source info
% 1.99/0.99  
% 1.99/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.99/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/0.99  git: non_committed_changes: false
% 1.99/0.99  git: last_make_outside_of_git: false
% 1.99/0.99  
% 1.99/0.99  ------ 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options
% 1.99/0.99  
% 1.99/0.99  --out_options                           all
% 1.99/0.99  --tptp_safe_out                         true
% 1.99/0.99  --problem_path                          ""
% 1.99/0.99  --include_path                          ""
% 1.99/0.99  --clausifier                            res/vclausify_rel
% 1.99/0.99  --clausifier_options                    --mode clausify
% 1.99/0.99  --stdin                                 false
% 1.99/0.99  --stats_out                             all
% 1.99/0.99  
% 1.99/0.99  ------ General Options
% 1.99/0.99  
% 1.99/0.99  --fof                                   false
% 1.99/0.99  --time_out_real                         305.
% 1.99/0.99  --time_out_virtual                      -1.
% 1.99/0.99  --symbol_type_check                     false
% 1.99/0.99  --clausify_out                          false
% 1.99/0.99  --sig_cnt_out                           false
% 1.99/0.99  --trig_cnt_out                          false
% 1.99/0.99  --trig_cnt_out_tolerance                1.
% 1.99/0.99  --trig_cnt_out_sk_spl                   false
% 1.99/0.99  --abstr_cl_out                          false
% 1.99/0.99  
% 1.99/0.99  ------ Global Options
% 1.99/0.99  
% 1.99/0.99  --schedule                              default
% 1.99/0.99  --add_important_lit                     false
% 1.99/0.99  --prop_solver_per_cl                    1000
% 1.99/0.99  --min_unsat_core                        false
% 1.99/0.99  --soft_assumptions                      false
% 1.99/0.99  --soft_lemma_size                       3
% 1.99/0.99  --prop_impl_unit_size                   0
% 1.99/0.99  --prop_impl_unit                        []
% 1.99/0.99  --share_sel_clauses                     true
% 1.99/0.99  --reset_solvers                         false
% 1.99/0.99  --bc_imp_inh                            [conj_cone]
% 1.99/0.99  --conj_cone_tolerance                   3.
% 1.99/0.99  --extra_neg_conj                        none
% 1.99/0.99  --large_theory_mode                     true
% 1.99/0.99  --prolific_symb_bound                   200
% 1.99/0.99  --lt_threshold                          2000
% 1.99/0.99  --clause_weak_htbl                      true
% 1.99/0.99  --gc_record_bc_elim                     false
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing Options
% 1.99/0.99  
% 1.99/0.99  --preprocessing_flag                    true
% 1.99/0.99  --time_out_prep_mult                    0.1
% 1.99/0.99  --splitting_mode                        input
% 1.99/0.99  --splitting_grd                         true
% 1.99/0.99  --splitting_cvd                         false
% 1.99/0.99  --splitting_cvd_svl                     false
% 1.99/0.99  --splitting_nvd                         32
% 1.99/0.99  --sub_typing                            true
% 1.99/0.99  --prep_gs_sim                           true
% 1.99/0.99  --prep_unflatten                        true
% 1.99/0.99  --prep_res_sim                          true
% 1.99/0.99  --prep_upred                            true
% 1.99/0.99  --prep_sem_filter                       exhaustive
% 1.99/0.99  --prep_sem_filter_out                   false
% 1.99/0.99  --pred_elim                             true
% 1.99/0.99  --res_sim_input                         true
% 1.99/0.99  --eq_ax_congr_red                       true
% 1.99/0.99  --pure_diseq_elim                       true
% 1.99/0.99  --brand_transform                       false
% 1.99/0.99  --non_eq_to_eq                          false
% 1.99/0.99  --prep_def_merge                        true
% 1.99/0.99  --prep_def_merge_prop_impl              false
% 1.99/0.99  --prep_def_merge_mbd                    true
% 1.99/0.99  --prep_def_merge_tr_red                 false
% 1.99/0.99  --prep_def_merge_tr_cl                  false
% 1.99/0.99  --smt_preprocessing                     true
% 1.99/0.99  --smt_ac_axioms                         fast
% 1.99/0.99  --preprocessed_out                      false
% 1.99/0.99  --preprocessed_stats                    false
% 1.99/0.99  
% 1.99/0.99  ------ Abstraction refinement Options
% 1.99/0.99  
% 1.99/0.99  --abstr_ref                             []
% 1.99/0.99  --abstr_ref_prep                        false
% 1.99/0.99  --abstr_ref_until_sat                   false
% 1.99/0.99  --abstr_ref_sig_restrict                funpre
% 1.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.99  --abstr_ref_under                       []
% 1.99/0.99  
% 1.99/0.99  ------ SAT Options
% 1.99/0.99  
% 1.99/0.99  --sat_mode                              false
% 1.99/0.99  --sat_fm_restart_options                ""
% 1.99/0.99  --sat_gr_def                            false
% 1.99/0.99  --sat_epr_types                         true
% 1.99/0.99  --sat_non_cyclic_types                  false
% 1.99/0.99  --sat_finite_models                     false
% 1.99/0.99  --sat_fm_lemmas                         false
% 1.99/0.99  --sat_fm_prep                           false
% 1.99/0.99  --sat_fm_uc_incr                        true
% 1.99/0.99  --sat_out_model                         small
% 1.99/0.99  --sat_out_clauses                       false
% 1.99/0.99  
% 1.99/0.99  ------ QBF Options
% 1.99/0.99  
% 1.99/0.99  --qbf_mode                              false
% 1.99/0.99  --qbf_elim_univ                         false
% 1.99/0.99  --qbf_dom_inst                          none
% 1.99/0.99  --qbf_dom_pre_inst                      false
% 1.99/0.99  --qbf_sk_in                             false
% 1.99/0.99  --qbf_pred_elim                         true
% 1.99/0.99  --qbf_split                             512
% 1.99/0.99  
% 1.99/0.99  ------ BMC1 Options
% 1.99/0.99  
% 1.99/0.99  --bmc1_incremental                      false
% 1.99/0.99  --bmc1_axioms                           reachable_all
% 1.99/0.99  --bmc1_min_bound                        0
% 1.99/0.99  --bmc1_max_bound                        -1
% 1.99/0.99  --bmc1_max_bound_default                -1
% 1.99/0.99  --bmc1_symbol_reachability              true
% 1.99/0.99  --bmc1_property_lemmas                  false
% 1.99/0.99  --bmc1_k_induction                      false
% 1.99/0.99  --bmc1_non_equiv_states                 false
% 1.99/0.99  --bmc1_deadlock                         false
% 1.99/0.99  --bmc1_ucm                              false
% 1.99/0.99  --bmc1_add_unsat_core                   none
% 1.99/0.99  --bmc1_unsat_core_children              false
% 1.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.99  --bmc1_out_stat                         full
% 1.99/0.99  --bmc1_ground_init                      false
% 1.99/0.99  --bmc1_pre_inst_next_state              false
% 1.99/0.99  --bmc1_pre_inst_state                   false
% 1.99/0.99  --bmc1_pre_inst_reach_state             false
% 1.99/0.99  --bmc1_out_unsat_core                   false
% 1.99/0.99  --bmc1_aig_witness_out                  false
% 1.99/0.99  --bmc1_verbose                          false
% 1.99/0.99  --bmc1_dump_clauses_tptp                false
% 1.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.99  --bmc1_dump_file                        -
% 1.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.99  --bmc1_ucm_extend_mode                  1
% 1.99/0.99  --bmc1_ucm_init_mode                    2
% 1.99/0.99  --bmc1_ucm_cone_mode                    none
% 1.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.99  --bmc1_ucm_relax_model                  4
% 1.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.99  --bmc1_ucm_layered_model                none
% 1.99/0.99  --bmc1_ucm_max_lemma_size               10
% 1.99/0.99  
% 1.99/0.99  ------ AIG Options
% 1.99/0.99  
% 1.99/0.99  --aig_mode                              false
% 1.99/0.99  
% 1.99/0.99  ------ Instantiation Options
% 1.99/0.99  
% 1.99/0.99  --instantiation_flag                    true
% 1.99/0.99  --inst_sos_flag                         false
% 1.99/0.99  --inst_sos_phase                        true
% 1.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel_side                     num_symb
% 1.99/0.99  --inst_solver_per_active                1400
% 1.99/0.99  --inst_solver_calls_frac                1.
% 1.99/0.99  --inst_passive_queue_type               priority_queues
% 1.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.99  --inst_passive_queues_freq              [25;2]
% 1.99/0.99  --inst_dismatching                      true
% 1.99/0.99  --inst_eager_unprocessed_to_passive     true
% 1.99/0.99  --inst_prop_sim_given                   true
% 1.99/0.99  --inst_prop_sim_new                     false
% 1.99/0.99  --inst_subs_new                         false
% 1.99/0.99  --inst_eq_res_simp                      false
% 1.99/0.99  --inst_subs_given                       false
% 1.99/0.99  --inst_orphan_elimination               true
% 1.99/0.99  --inst_learning_loop_flag               true
% 1.99/0.99  --inst_learning_start                   3000
% 1.99/0.99  --inst_learning_factor                  2
% 1.99/0.99  --inst_start_prop_sim_after_learn       3
% 1.99/0.99  --inst_sel_renew                        solver
% 1.99/0.99  --inst_lit_activity_flag                true
% 1.99/0.99  --inst_restr_to_given                   false
% 1.99/0.99  --inst_activity_threshold               500
% 1.99/0.99  --inst_out_proof                        true
% 1.99/0.99  
% 1.99/0.99  ------ Resolution Options
% 1.99/0.99  
% 1.99/0.99  --resolution_flag                       true
% 1.99/0.99  --res_lit_sel                           adaptive
% 1.99/0.99  --res_lit_sel_side                      none
% 1.99/0.99  --res_ordering                          kbo
% 1.99/0.99  --res_to_prop_solver                    active
% 1.99/0.99  --res_prop_simpl_new                    false
% 1.99/0.99  --res_prop_simpl_given                  true
% 1.99/0.99  --res_passive_queue_type                priority_queues
% 1.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.99  --res_passive_queues_freq               [15;5]
% 1.99/0.99  --res_forward_subs                      full
% 1.99/0.99  --res_backward_subs                     full
% 1.99/0.99  --res_forward_subs_resolution           true
% 1.99/0.99  --res_backward_subs_resolution          true
% 1.99/0.99  --res_orphan_elimination                true
% 1.99/0.99  --res_time_limit                        2.
% 1.99/0.99  --res_out_proof                         true
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Options
% 1.99/0.99  
% 1.99/0.99  --superposition_flag                    true
% 1.99/0.99  --sup_passive_queue_type                priority_queues
% 1.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.99  --demod_completeness_check              fast
% 1.99/0.99  --demod_use_ground                      true
% 1.99/0.99  --sup_to_prop_solver                    passive
% 1.99/0.99  --sup_prop_simpl_new                    true
% 1.99/0.99  --sup_prop_simpl_given                  true
% 1.99/0.99  --sup_fun_splitting                     false
% 1.99/0.99  --sup_smt_interval                      50000
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Simplification Setup
% 1.99/0.99  
% 1.99/0.99  --sup_indices_passive                   []
% 1.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_full_bw                           [BwDemod]
% 1.99/0.99  --sup_immed_triv                        [TrivRules]
% 1.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_immed_bw_main                     []
% 1.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  
% 1.99/0.99  ------ Combination Options
% 1.99/0.99  
% 1.99/0.99  --comb_res_mult                         3
% 1.99/0.99  --comb_sup_mult                         2
% 1.99/0.99  --comb_inst_mult                        10
% 1.99/0.99  
% 1.99/0.99  ------ Debug Options
% 1.99/0.99  
% 1.99/0.99  --dbg_backtrace                         false
% 1.99/0.99  --dbg_dump_prop_clauses                 false
% 1.99/0.99  --dbg_dump_prop_clauses_file            -
% 1.99/0.99  --dbg_out_stat                          false
% 1.99/0.99  ------ Parsing...
% 1.99/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/0.99  ------ Proving...
% 1.99/0.99  ------ Problem Properties 
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  clauses                                 16
% 1.99/0.99  conjectures                             2
% 1.99/0.99  EPR                                     0
% 1.99/0.99  Horn                                    12
% 1.99/0.99  unary                                   7
% 1.99/0.99  binary                                  1
% 1.99/0.99  lits                                    57
% 1.99/0.99  lits eq                                 21
% 1.99/0.99  fd_pure                                 0
% 1.99/0.99  fd_pseudo                               0
% 1.99/0.99  fd_cond                                 0
% 1.99/0.99  fd_pseudo_cond                          0
% 1.99/0.99  AC symbols                              0
% 1.99/0.99  
% 1.99/0.99  ------ Schedule dynamic 5 is on 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  ------ 
% 1.99/0.99  Current options:
% 1.99/0.99  ------ 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options
% 1.99/0.99  
% 1.99/0.99  --out_options                           all
% 1.99/0.99  --tptp_safe_out                         true
% 1.99/0.99  --problem_path                          ""
% 1.99/0.99  --include_path                          ""
% 1.99/0.99  --clausifier                            res/vclausify_rel
% 1.99/0.99  --clausifier_options                    --mode clausify
% 1.99/0.99  --stdin                                 false
% 1.99/0.99  --stats_out                             all
% 1.99/0.99  
% 1.99/0.99  ------ General Options
% 1.99/0.99  
% 1.99/0.99  --fof                                   false
% 1.99/0.99  --time_out_real                         305.
% 1.99/0.99  --time_out_virtual                      -1.
% 1.99/0.99  --symbol_type_check                     false
% 1.99/0.99  --clausify_out                          false
% 1.99/0.99  --sig_cnt_out                           false
% 1.99/0.99  --trig_cnt_out                          false
% 1.99/0.99  --trig_cnt_out_tolerance                1.
% 1.99/0.99  --trig_cnt_out_sk_spl                   false
% 1.99/0.99  --abstr_cl_out                          false
% 1.99/0.99  
% 1.99/0.99  ------ Global Options
% 1.99/0.99  
% 1.99/0.99  --schedule                              default
% 1.99/0.99  --add_important_lit                     false
% 1.99/0.99  --prop_solver_per_cl                    1000
% 1.99/0.99  --min_unsat_core                        false
% 1.99/0.99  --soft_assumptions                      false
% 1.99/0.99  --soft_lemma_size                       3
% 1.99/0.99  --prop_impl_unit_size                   0
% 1.99/0.99  --prop_impl_unit                        []
% 1.99/0.99  --share_sel_clauses                     true
% 1.99/0.99  --reset_solvers                         false
% 1.99/0.99  --bc_imp_inh                            [conj_cone]
% 1.99/0.99  --conj_cone_tolerance                   3.
% 1.99/0.99  --extra_neg_conj                        none
% 1.99/0.99  --large_theory_mode                     true
% 1.99/0.99  --prolific_symb_bound                   200
% 1.99/0.99  --lt_threshold                          2000
% 1.99/0.99  --clause_weak_htbl                      true
% 1.99/0.99  --gc_record_bc_elim                     false
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing Options
% 1.99/0.99  
% 1.99/0.99  --preprocessing_flag                    true
% 1.99/0.99  --time_out_prep_mult                    0.1
% 1.99/0.99  --splitting_mode                        input
% 1.99/0.99  --splitting_grd                         true
% 1.99/0.99  --splitting_cvd                         false
% 1.99/0.99  --splitting_cvd_svl                     false
% 1.99/0.99  --splitting_nvd                         32
% 1.99/0.99  --sub_typing                            true
% 1.99/0.99  --prep_gs_sim                           true
% 1.99/0.99  --prep_unflatten                        true
% 1.99/0.99  --prep_res_sim                          true
% 1.99/0.99  --prep_upred                            true
% 1.99/0.99  --prep_sem_filter                       exhaustive
% 1.99/0.99  --prep_sem_filter_out                   false
% 1.99/0.99  --pred_elim                             true
% 1.99/0.99  --res_sim_input                         true
% 1.99/0.99  --eq_ax_congr_red                       true
% 1.99/0.99  --pure_diseq_elim                       true
% 1.99/0.99  --brand_transform                       false
% 1.99/0.99  --non_eq_to_eq                          false
% 1.99/0.99  --prep_def_merge                        true
% 1.99/0.99  --prep_def_merge_prop_impl              false
% 1.99/0.99  --prep_def_merge_mbd                    true
% 1.99/0.99  --prep_def_merge_tr_red                 false
% 1.99/0.99  --prep_def_merge_tr_cl                  false
% 1.99/0.99  --smt_preprocessing                     true
% 1.99/0.99  --smt_ac_axioms                         fast
% 1.99/0.99  --preprocessed_out                      false
% 1.99/0.99  --preprocessed_stats                    false
% 1.99/0.99  
% 1.99/0.99  ------ Abstraction refinement Options
% 1.99/0.99  
% 1.99/0.99  --abstr_ref                             []
% 1.99/0.99  --abstr_ref_prep                        false
% 1.99/0.99  --abstr_ref_until_sat                   false
% 1.99/0.99  --abstr_ref_sig_restrict                funpre
% 1.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.99  --abstr_ref_under                       []
% 1.99/0.99  
% 1.99/0.99  ------ SAT Options
% 1.99/0.99  
% 1.99/0.99  --sat_mode                              false
% 1.99/0.99  --sat_fm_restart_options                ""
% 1.99/0.99  --sat_gr_def                            false
% 1.99/0.99  --sat_epr_types                         true
% 1.99/0.99  --sat_non_cyclic_types                  false
% 1.99/0.99  --sat_finite_models                     false
% 1.99/0.99  --sat_fm_lemmas                         false
% 1.99/0.99  --sat_fm_prep                           false
% 1.99/0.99  --sat_fm_uc_incr                        true
% 1.99/0.99  --sat_out_model                         small
% 1.99/0.99  --sat_out_clauses                       false
% 1.99/0.99  
% 1.99/0.99  ------ QBF Options
% 1.99/0.99  
% 1.99/0.99  --qbf_mode                              false
% 1.99/0.99  --qbf_elim_univ                         false
% 1.99/0.99  --qbf_dom_inst                          none
% 1.99/0.99  --qbf_dom_pre_inst                      false
% 1.99/0.99  --qbf_sk_in                             false
% 1.99/0.99  --qbf_pred_elim                         true
% 1.99/0.99  --qbf_split                             512
% 1.99/0.99  
% 1.99/0.99  ------ BMC1 Options
% 1.99/0.99  
% 1.99/0.99  --bmc1_incremental                      false
% 1.99/0.99  --bmc1_axioms                           reachable_all
% 1.99/0.99  --bmc1_min_bound                        0
% 1.99/0.99  --bmc1_max_bound                        -1
% 1.99/0.99  --bmc1_max_bound_default                -1
% 1.99/0.99  --bmc1_symbol_reachability              true
% 1.99/0.99  --bmc1_property_lemmas                  false
% 1.99/0.99  --bmc1_k_induction                      false
% 1.99/0.99  --bmc1_non_equiv_states                 false
% 1.99/0.99  --bmc1_deadlock                         false
% 1.99/0.99  --bmc1_ucm                              false
% 1.99/0.99  --bmc1_add_unsat_core                   none
% 1.99/0.99  --bmc1_unsat_core_children              false
% 1.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.99  --bmc1_out_stat                         full
% 1.99/0.99  --bmc1_ground_init                      false
% 1.99/0.99  --bmc1_pre_inst_next_state              false
% 1.99/0.99  --bmc1_pre_inst_state                   false
% 1.99/0.99  --bmc1_pre_inst_reach_state             false
% 1.99/0.99  --bmc1_out_unsat_core                   false
% 1.99/0.99  --bmc1_aig_witness_out                  false
% 1.99/0.99  --bmc1_verbose                          false
% 1.99/0.99  --bmc1_dump_clauses_tptp                false
% 1.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.99  --bmc1_dump_file                        -
% 1.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.99  --bmc1_ucm_extend_mode                  1
% 1.99/0.99  --bmc1_ucm_init_mode                    2
% 1.99/0.99  --bmc1_ucm_cone_mode                    none
% 1.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.99  --bmc1_ucm_relax_model                  4
% 1.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.99  --bmc1_ucm_layered_model                none
% 1.99/0.99  --bmc1_ucm_max_lemma_size               10
% 1.99/0.99  
% 1.99/0.99  ------ AIG Options
% 1.99/0.99  
% 1.99/0.99  --aig_mode                              false
% 1.99/0.99  
% 1.99/0.99  ------ Instantiation Options
% 1.99/0.99  
% 1.99/0.99  --instantiation_flag                    true
% 1.99/0.99  --inst_sos_flag                         false
% 1.99/0.99  --inst_sos_phase                        true
% 1.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel_side                     none
% 1.99/0.99  --inst_solver_per_active                1400
% 1.99/0.99  --inst_solver_calls_frac                1.
% 1.99/0.99  --inst_passive_queue_type               priority_queues
% 1.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.99  --inst_passive_queues_freq              [25;2]
% 1.99/0.99  --inst_dismatching                      true
% 1.99/0.99  --inst_eager_unprocessed_to_passive     true
% 1.99/0.99  --inst_prop_sim_given                   true
% 1.99/0.99  --inst_prop_sim_new                     false
% 1.99/0.99  --inst_subs_new                         false
% 1.99/0.99  --inst_eq_res_simp                      false
% 1.99/0.99  --inst_subs_given                       false
% 1.99/0.99  --inst_orphan_elimination               true
% 1.99/0.99  --inst_learning_loop_flag               true
% 1.99/0.99  --inst_learning_start                   3000
% 1.99/0.99  --inst_learning_factor                  2
% 1.99/0.99  --inst_start_prop_sim_after_learn       3
% 1.99/0.99  --inst_sel_renew                        solver
% 1.99/0.99  --inst_lit_activity_flag                true
% 1.99/0.99  --inst_restr_to_given                   false
% 1.99/0.99  --inst_activity_threshold               500
% 1.99/0.99  --inst_out_proof                        true
% 1.99/0.99  
% 1.99/0.99  ------ Resolution Options
% 1.99/0.99  
% 1.99/0.99  --resolution_flag                       false
% 1.99/0.99  --res_lit_sel                           adaptive
% 1.99/0.99  --res_lit_sel_side                      none
% 1.99/0.99  --res_ordering                          kbo
% 1.99/0.99  --res_to_prop_solver                    active
% 1.99/0.99  --res_prop_simpl_new                    false
% 1.99/0.99  --res_prop_simpl_given                  true
% 1.99/0.99  --res_passive_queue_type                priority_queues
% 1.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.99  --res_passive_queues_freq               [15;5]
% 1.99/0.99  --res_forward_subs                      full
% 1.99/0.99  --res_backward_subs                     full
% 1.99/0.99  --res_forward_subs_resolution           true
% 1.99/0.99  --res_backward_subs_resolution          true
% 1.99/0.99  --res_orphan_elimination                true
% 1.99/0.99  --res_time_limit                        2.
% 1.99/0.99  --res_out_proof                         true
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Options
% 1.99/0.99  
% 1.99/0.99  --superposition_flag                    true
% 1.99/0.99  --sup_passive_queue_type                priority_queues
% 1.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.99  --demod_completeness_check              fast
% 1.99/0.99  --demod_use_ground                      true
% 1.99/0.99  --sup_to_prop_solver                    passive
% 1.99/0.99  --sup_prop_simpl_new                    true
% 1.99/0.99  --sup_prop_simpl_given                  true
% 1.99/0.99  --sup_fun_splitting                     false
% 1.99/0.99  --sup_smt_interval                      50000
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Simplification Setup
% 1.99/0.99  
% 1.99/0.99  --sup_indices_passive                   []
% 1.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_full_bw                           [BwDemod]
% 1.99/0.99  --sup_immed_triv                        [TrivRules]
% 1.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_immed_bw_main                     []
% 1.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  
% 1.99/0.99  ------ Combination Options
% 1.99/0.99  
% 1.99/0.99  --comb_res_mult                         3
% 1.99/0.99  --comb_sup_mult                         2
% 1.99/0.99  --comb_inst_mult                        10
% 1.99/0.99  
% 1.99/0.99  ------ Debug Options
% 1.99/0.99  
% 1.99/0.99  --dbg_backtrace                         false
% 1.99/0.99  --dbg_dump_prop_clauses                 false
% 1.99/0.99  --dbg_dump_prop_clauses_file            -
% 1.99/0.99  --dbg_out_stat                          false
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  ------ Proving...
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  % SZS status Theorem for theBenchmark.p
% 1.99/0.99  
% 1.99/0.99   Resolution empty clause
% 1.99/0.99  
% 1.99/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  fof(f13,conjecture,(
% 1.99/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f14,negated_conjecture,(
% 1.99/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.99/0.99    inference(negated_conjecture,[],[f13])).
% 1.99/0.99  
% 1.99/0.99  fof(f34,plain,(
% 1.99/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f14])).
% 1.99/0.99  
% 1.99/0.99  fof(f35,plain,(
% 1.99/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f34])).
% 1.99/0.99  
% 1.99/0.99  fof(f38,plain,(
% 1.99/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.99/0.99    inference(nnf_transformation,[],[f35])).
% 1.99/0.99  
% 1.99/0.99  fof(f39,plain,(
% 1.99/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f38])).
% 1.99/0.99  
% 1.99/0.99  fof(f42,plain,(
% 1.99/0.99    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & (r1_waybel_7(X0,X1,sK2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.99/0.99    introduced(choice_axiom,[])).
% 1.99/0.99  
% 1.99/0.99  fof(f41,plain,(
% 1.99/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & (r1_waybel_7(X0,sK1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK1))) )),
% 1.99/0.99    introduced(choice_axiom,[])).
% 1.99/0.99  
% 1.99/0.99  fof(f40,plain,(
% 1.99/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.99/0.99    introduced(choice_axiom,[])).
% 1.99/0.99  
% 1.99/0.99  fof(f43,plain,(
% 1.99/0.99    (((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.99/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42,f41,f40])).
% 1.99/0.99  
% 1.99/0.99  fof(f66,plain,(
% 1.99/0.99    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.99/0.99    inference(cnf_transformation,[],[f43])).
% 1.99/0.99  
% 1.99/0.99  fof(f6,axiom,(
% 1.99/0.99    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f49,plain,(
% 1.99/0.99    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.99/0.99    inference(cnf_transformation,[],[f6])).
% 1.99/0.99  
% 1.99/0.99  fof(f81,plain,(
% 1.99/0.99    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.99/0.99    inference(definition_unfolding,[],[f66,f49])).
% 1.99/0.99  
% 1.99/0.99  fof(f8,axiom,(
% 1.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f17,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/0.99    inference(pure_predicate_removal,[],[f8])).
% 1.99/0.99  
% 1.99/0.99  fof(f24,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f17])).
% 1.99/0.99  
% 1.99/0.99  fof(f25,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f24])).
% 1.99/0.99  
% 1.99/0.99  fof(f53,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f25])).
% 1.99/0.99  
% 1.99/0.99  fof(f72,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(definition_unfolding,[],[f53,f49,f49,f49])).
% 1.99/0.99  
% 1.99/0.99  fof(f71,plain,(
% 1.99/0.99    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.99/0.99    inference(cnf_transformation,[],[f43])).
% 1.99/0.99  
% 1.99/0.99  fof(f11,axiom,(
% 1.99/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f30,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f11])).
% 1.99/0.99  
% 1.99/0.99  fof(f31,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f30])).
% 1.99/0.99  
% 1.99/0.99  fof(f37,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(nnf_transformation,[],[f31])).
% 1.99/0.99  
% 1.99/0.99  fof(f59,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f37])).
% 1.99/0.99  
% 1.99/0.99  fof(f62,plain,(
% 1.99/0.99    v2_pre_topc(sK0)),
% 1.99/0.99    inference(cnf_transformation,[],[f43])).
% 1.99/0.99  
% 1.99/0.99  fof(f61,plain,(
% 1.99/0.99    ~v2_struct_0(sK0)),
% 1.99/0.99    inference(cnf_transformation,[],[f43])).
% 1.99/0.99  
% 1.99/0.99  fof(f63,plain,(
% 1.99/0.99    l1_pre_topc(sK0)),
% 1.99/0.99    inference(cnf_transformation,[],[f43])).
% 1.99/0.99  
% 1.99/0.99  fof(f69,plain,(
% 1.99/0.99    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.99/0.99    inference(cnf_transformation,[],[f43])).
% 1.99/0.99  
% 1.99/0.99  fof(f4,axiom,(
% 1.99/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f20,plain,(
% 1.99/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.99/0.99    inference(ennf_transformation,[],[f4])).
% 1.99/0.99  
% 1.99/0.99  fof(f47,plain,(
% 1.99/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f20])).
% 1.99/0.99  
% 1.99/0.99  fof(f67,plain,(
% 1.99/0.99    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.99/0.99    inference(cnf_transformation,[],[f43])).
% 1.99/0.99  
% 1.99/0.99  fof(f80,plain,(
% 1.99/0.99    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.99/0.99    inference(definition_unfolding,[],[f67,f49])).
% 1.99/0.99  
% 1.99/0.99  fof(f64,plain,(
% 1.99/0.99    ~v1_xboole_0(sK1)),
% 1.99/0.99    inference(cnf_transformation,[],[f43])).
% 1.99/0.99  
% 1.99/0.99  fof(f5,axiom,(
% 1.99/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f21,plain,(
% 1.99/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f5])).
% 1.99/0.99  
% 1.99/0.99  fof(f22,plain,(
% 1.99/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f21])).
% 1.99/0.99  
% 1.99/0.99  fof(f48,plain,(
% 1.99/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f22])).
% 1.99/0.99  
% 1.99/0.99  fof(f9,axiom,(
% 1.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f15,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/0.99    inference(pure_predicate_removal,[],[f9])).
% 1.99/0.99  
% 1.99/0.99  fof(f18,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/0.99    inference(pure_predicate_removal,[],[f15])).
% 1.99/0.99  
% 1.99/0.99  fof(f26,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f18])).
% 1.99/0.99  
% 1.99/0.99  fof(f27,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f26])).
% 1.99/0.99  
% 1.99/0.99  fof(f55,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f27])).
% 1.99/0.99  
% 1.99/0.99  fof(f74,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(definition_unfolding,[],[f55,f49,f49,f49])).
% 1.99/0.99  
% 1.99/0.99  fof(f52,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f25])).
% 1.99/0.99  
% 1.99/0.99  fof(f73,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(definition_unfolding,[],[f52,f49,f49,f49])).
% 1.99/0.99  
% 1.99/0.99  fof(f3,axiom,(
% 1.99/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f19,plain,(
% 1.99/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.99/0.99    inference(ennf_transformation,[],[f3])).
% 1.99/0.99  
% 1.99/0.99  fof(f46,plain,(
% 1.99/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f19])).
% 1.99/0.99  
% 1.99/0.99  fof(f65,plain,(
% 1.99/0.99    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.99/0.99    inference(cnf_transformation,[],[f43])).
% 1.99/0.99  
% 1.99/0.99  fof(f82,plain,(
% 1.99/0.99    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.99/0.99    inference(definition_unfolding,[],[f65,f49])).
% 1.99/0.99  
% 1.99/0.99  fof(f12,axiom,(
% 1.99/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f32,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f12])).
% 1.99/0.99  
% 1.99/0.99  fof(f33,plain,(
% 1.99/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f32])).
% 1.99/0.99  
% 1.99/0.99  fof(f60,plain,(
% 1.99/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f33])).
% 1.99/0.99  
% 1.99/0.99  fof(f78,plain,(
% 1.99/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(definition_unfolding,[],[f60,f49,f49,f49,f49])).
% 1.99/0.99  
% 1.99/0.99  fof(f68,plain,(
% 1.99/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.99/0.99    inference(cnf_transformation,[],[f43])).
% 1.99/0.99  
% 1.99/0.99  fof(f79,plain,(
% 1.99/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.99/0.99    inference(definition_unfolding,[],[f68,f49])).
% 1.99/0.99  
% 1.99/0.99  fof(f7,axiom,(
% 1.99/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f23,plain,(
% 1.99/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f7])).
% 1.99/0.99  
% 1.99/0.99  fof(f36,plain,(
% 1.99/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.99/0.99    inference(nnf_transformation,[],[f23])).
% 1.99/0.99  
% 1.99/0.99  fof(f51,plain,(
% 1.99/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.99/0.99    inference(cnf_transformation,[],[f36])).
% 1.99/0.99  
% 1.99/0.99  fof(f10,axiom,(
% 1.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f16,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/0.99    inference(pure_predicate_removal,[],[f10])).
% 1.99/0.99  
% 1.99/0.99  fof(f28,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.99/0.99    inference(ennf_transformation,[],[f16])).
% 1.99/0.99  
% 1.99/0.99  fof(f29,plain,(
% 1.99/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.99/0.99    inference(flattening,[],[f28])).
% 1.99/0.99  
% 1.99/0.99  fof(f57,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f29])).
% 1.99/0.99  
% 1.99/0.99  fof(f76,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(definition_unfolding,[],[f57,f49,f49,f49,f49])).
% 1.99/0.99  
% 1.99/0.99  fof(f1,axiom,(
% 1.99/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f44,plain,(
% 1.99/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.99/0.99    inference(cnf_transformation,[],[f1])).
% 1.99/0.99  
% 1.99/0.99  fof(f2,axiom,(
% 1.99/0.99    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 1.99/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/0.99  
% 1.99/0.99  fof(f45,plain,(
% 1.99/0.99    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f2])).
% 1.99/0.99  
% 1.99/0.99  fof(f70,plain,(
% 1.99/0.99    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.99/0.99    inference(cnf_transformation,[],[f43])).
% 1.99/0.99  
% 1.99/0.99  fof(f58,plain,(
% 1.99/0.99    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.99/0.99    inference(cnf_transformation,[],[f37])).
% 1.99/0.99  
% 1.99/0.99  cnf(c_21,negated_conjecture,
% 1.99/0.99      ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.99/0.99      inference(cnf_transformation,[],[f81]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_7,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | v2_struct_0(X2)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | ~ l1_struct_0(X2) ),
% 1.99/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_16,negated_conjecture,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.99/0.99      inference(cnf_transformation,[],[f71]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_199,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.99/0.99      inference(prop_impl,[status(thm)],[c_16]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_13,plain,
% 1.99/0.99      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.99/0.99      | r3_waybel_9(X0,X1,X2)
% 1.99/0.99      | ~ l1_waybel_0(X1,X0)
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/0.99      | ~ v2_pre_topc(X0)
% 1.99/0.99      | ~ v7_waybel_0(X1)
% 1.99/0.99      | ~ v4_orders_2(X1)
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | ~ l1_pre_topc(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_25,negated_conjecture,
% 1.99/0.99      ( v2_pre_topc(sK0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_391,plain,
% 1.99/0.99      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.99/0.99      | r3_waybel_9(X0,X1,X2)
% 1.99/0.99      | ~ l1_waybel_0(X1,X0)
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/0.99      | ~ v7_waybel_0(X1)
% 1.99/0.99      | ~ v4_orders_2(X1)
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | ~ l1_pre_topc(X0)
% 1.99/0.99      | sK0 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_392,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.99/0.99      | r3_waybel_9(sK0,X0,X1)
% 1.99/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/0.99      | ~ v7_waybel_0(X0)
% 1.99/0.99      | ~ v4_orders_2(X0)
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | v2_struct_0(sK0)
% 1.99/0.99      | ~ l1_pre_topc(sK0) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_391]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_26,negated_conjecture,
% 1.99/0.99      ( ~ v2_struct_0(sK0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_24,negated_conjecture,
% 1.99/0.99      ( l1_pre_topc(sK0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_396,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.99/0.99      | r3_waybel_9(sK0,X0,X1)
% 1.99/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/0.99      | ~ v7_waybel_0(X0)
% 1.99/0.99      | ~ v4_orders_2(X0)
% 1.99/0.99      | v2_struct_0(X0) ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_392,c_26,c_24]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_673,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/0.99      | ~ v7_waybel_0(X0)
% 1.99/0.99      | ~ v4_orders_2(X0)
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 1.99/0.99      | sK2 != X1
% 1.99/0.99      | sK0 != sK0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_199,c_396]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_674,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.99/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_673]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_18,negated_conjecture,
% 1.99/0.99      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 1.99/0.99      inference(cnf_transformation,[],[f69]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_676,plain,
% 1.99/0.99      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_674,c_18]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_677,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_676]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_713,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(X2)
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | ~ l1_struct_0(X2)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 1.99/0.99      | sK0 != X2 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_677]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_714,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(sK0)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | ~ l1_struct_0(sK0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_713]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_3,plain,
% 1.99/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_73,plain,
% 1.99/0.99      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_718,plain,
% 1.99/0.99      ( v1_xboole_0(X0)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_714,c_26,c_24,c_73]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_719,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_718]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_20,negated_conjecture,
% 1.99/0.99      ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.99/0.99      inference(cnf_transformation,[],[f80]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1403,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.99/0.99      | sK1 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_719,c_20]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1404,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | v1_xboole_0(sK1)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_1403]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_23,negated_conjecture,
% 1.99/0.99      ( ~ v1_xboole_0(sK1) ),
% 1.99/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1408,plain,
% 1.99/0.99      ( v1_xboole_0(X0)
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1404,c_23]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1409,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_1408]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1644,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | sK1 != sK1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_1409]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4,plain,
% 1.99/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_440,plain,
% 1.99/0.99      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_441,plain,
% 1.99/0.99      ( l1_struct_0(sK0) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_440]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_811,plain,
% 1.99/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK0 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_441]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_812,plain,
% 1.99/0.99      ( v2_struct_0(sK0) | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_811]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_70,plain,
% 1.99/0.99      ( v2_struct_0(sK0)
% 1.99/0.99      | ~ v1_xboole_0(u1_struct_0(sK0))
% 1.99/0.99      | ~ l1_struct_0(sK0) ),
% 1.99/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_814,plain,
% 1.99/0.99      ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_812,c_26,c_24,c_70,c_73]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2526,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | u1_struct_0(sK0) != X0
% 1.99/0.99      | sK1 != sK1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_1644,c_814]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2527,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_2526]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_9,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.99/0.99      | v2_struct_0(X2)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | ~ l1_struct_0(X2) ),
% 1.99/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_863,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.99/0.99      | v2_struct_0(X2)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | sK0 != X2 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_441]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_864,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | v2_struct_0(sK0)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_863]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_868,plain,
% 1.99/0.99      ( v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0) ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_864,c_26]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_869,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_868]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1328,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.99/0.99      | sK1 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_869,c_20]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1329,plain,
% 1.99/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | v1_xboole_0(sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_1328]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1333,plain,
% 1.99/0.99      ( v1_xboole_0(X0)
% 1.99/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1329,c_23]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1334,plain,
% 1.99/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_1333]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1720,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | sK1 != sK1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_1334]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2479,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | u1_struct_0(sK0) != X0
% 1.99/0.99      | sK1 != sK1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_1720,c_814]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2480,plain,
% 1.99/0.99      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.99/0.99      | v4_orders_2(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_2479]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2792,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_2527,c_2480]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_8,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | v2_struct_0(X2)
% 1.99/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | ~ l1_struct_0(X2) ),
% 1.99/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_896,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | v2_struct_0(X2)
% 1.99/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | sK0 != X2 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_441]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_897,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | v2_struct_0(sK0)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_896]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_901,plain,
% 1.99/0.99      ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0) ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_897,c_26]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_902,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_901]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1298,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.99/0.99      | sK1 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_902,c_20]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1299,plain,
% 1.99/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | v1_xboole_0(sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_1298]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1303,plain,
% 1.99/0.99      ( v1_xboole_0(X0)
% 1.99/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1299,c_23]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1304,plain,
% 1.99/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_1303]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1743,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | sK1 != sK1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_1304]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2463,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | u1_struct_0(sK0) != X0
% 1.99/0.99      | sK1 != sK1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_1743,c_814]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2464,plain,
% 1.99/0.99      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.99/0.99      | ~ v2_struct_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_2463]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_3146,plain,
% 1.99/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_2792,c_2464]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4245,plain,
% 1.99/0.99      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/0.99      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.99/0.99      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.99/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_3146]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2,plain,
% 1.99/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_822,plain,
% 1.99/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_441]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_823,plain,
% 1.99/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_822]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_22,negated_conjecture,
% 1.99/0.99      ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
% 1.99/0.99      inference(cnf_transformation,[],[f82]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_15,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.99/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | ~ l1_struct_0(X1)
% 1.99/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 1.99/0.99      inference(cnf_transformation,[],[f78]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_929,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.99/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 1.99/0.99      | sK0 != X1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_441]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_930,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.99/0.99      | v2_struct_0(sK0)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_929]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_934,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.99/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_930,c_26]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_935,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_934]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1109,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/0.99      | sK1 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_935]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1110,plain,
% 1.99/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.99/0.99      | v1_xboole_0(sK1)
% 1.99/0.99      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_1109]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_19,negated_conjecture,
% 1.99/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
% 1.99/0.99      inference(cnf_transformation,[],[f79]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1112,plain,
% 1.99/0.99      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_1110,c_23,c_21,c_20,c_19]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4342,plain,
% 1.99/0.99      ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.99/0.99      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
% 1.99/0.99      inference(light_normalisation,[status(thm)],[c_4245,c_823,c_1112]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4343,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.99/0.99      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
% 1.99/0.99      inference(equality_resolution_simp,[status(thm)],[c_4342]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_5,plain,
% 1.99/0.99      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 1.99/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_11,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.99/0.99      | v2_struct_0(X2)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | ~ l1_struct_0(X2) ),
% 1.99/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_827,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.99/0.99      | v2_struct_0(X2)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | sK0 != X2 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_441]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_828,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | v2_struct_0(sK0)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_827]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_832,plain,
% 1.99/0.99      ( v7_waybel_0(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0) ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_828,c_26]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_833,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_832]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1012,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | X0 != X2
% 1.99/0.99      | X3 = X2
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X1))) != X3 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_833]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1013,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X1))) = X0 ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_1012]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1265,plain,
% 1.99/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,X1,X0))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X1))) = X0
% 1.99/0.99      | sK1 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_1013,c_20]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1266,plain,
% 1.99/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | v1_xboole_0(sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK1 ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_1265]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1270,plain,
% 1.99/0.99      ( v1_xboole_0(X0)
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK1 ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1266,c_23]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1271,plain,
% 1.99/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK1 ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_1270]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1766,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK1
% 1.99/0.99      | sK1 != sK1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_1271]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2444,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK1
% 1.99/0.99      | u1_struct_0(sK0) != X0
% 1.99/0.99      | sK1 != sK1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_1766,c_814]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2445,plain,
% 1.99/0.99      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) = sK1 ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_2444]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4250,plain,
% 1.99/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) = sK1
% 1.99/0.99      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.99/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1)) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_2445]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4288,plain,
% 1.99/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) = sK1
% 1.99/0.99      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
% 1.99/0.99      inference(light_normalisation,[status(thm)],[c_4250,c_823]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4289,plain,
% 1.99/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) = sK1
% 1.99/0.99      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
% 1.99/0.99      inference(equality_resolution_simp,[status(thm)],[c_4288]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4254,plain,
% 1.99/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_0,plain,
% 1.99/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.99/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4256,plain,
% 1.99/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1,plain,
% 1.99/0.99      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_994,plain,
% 1.99/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.99/0.99      | X1 != X2
% 1.99/0.99      | X1 = X0
% 1.99/0.99      | k2_subset_1(X2) != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_5]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_995,plain,
% 1.99/0.99      ( ~ m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) | X0 = k2_subset_1(X0) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_994]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_999,plain,
% 1.99/0.99      ( X0 = k2_subset_1(X0) ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_995,c_0]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4264,plain,
% 1.99/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.99/0.99      inference(light_normalisation,[status(thm)],[c_4256,c_999]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1005,plain,
% 1.99/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != X0
% 1.99/0.99      | k2_subset_1(X0) != sK1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_22]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1006,plain,
% 1.99/0.99      ( k2_subset_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) != sK1 ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_1005]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4269,plain,
% 1.99/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != sK1 ),
% 1.99/0.99      inference(demodulation,[status(thm)],[c_1006,c_999]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4294,plain,
% 1.99/0.99      ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
% 1.99/0.99      inference(forward_subsumption_resolution,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_4289,c_4254,c_4264,c_4269]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_17,negated_conjecture,
% 1.99/0.99      ( r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.99/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_201,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.99/0.99      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_14,plain,
% 1.99/0.99      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.99/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 1.99/0.99      | ~ l1_waybel_0(X1,X0)
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/0.99      | ~ v2_pre_topc(X0)
% 1.99/0.99      | ~ v7_waybel_0(X1)
% 1.99/0.99      | ~ v4_orders_2(X1)
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | ~ l1_pre_topc(X0) ),
% 1.99/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_358,plain,
% 1.99/0.99      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.99/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 1.99/0.99      | ~ l1_waybel_0(X1,X0)
% 1.99/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/0.99      | ~ v7_waybel_0(X1)
% 1.99/0.99      | ~ v4_orders_2(X1)
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | v2_struct_0(X1)
% 1.99/0.99      | ~ l1_pre_topc(X0)
% 1.99/0.99      | sK0 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_359,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.99/0.99      | ~ r3_waybel_9(sK0,X0,X1)
% 1.99/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/0.99      | ~ v7_waybel_0(X0)
% 1.99/0.99      | ~ v4_orders_2(X0)
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | v2_struct_0(sK0)
% 1.99/0.99      | ~ l1_pre_topc(sK0) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_363,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.99/0.99      | ~ r3_waybel_9(sK0,X0,X1)
% 1.99/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/0.99      | ~ v7_waybel_0(X0)
% 1.99/0.99      | ~ v4_orders_2(X0)
% 1.99/0.99      | v2_struct_0(X0) ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_359,c_26,c_24]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_647,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.99/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/0.99      | ~ v7_waybel_0(X0)
% 1.99/0.99      | ~ v4_orders_2(X0)
% 1.99/0.99      | v2_struct_0(X0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 1.99/0.99      | sK2 != X1
% 1.99/0.99      | sK0 != sK0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_201,c_363]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_648,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.99/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_647]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_650,plain,
% 1.99/0.99      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_648,c_18]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_651,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_650]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_761,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(X2)
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | ~ l1_struct_0(X2)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 1.99/0.99      | sK0 != X2 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_651]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_762,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(sK0)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | ~ l1_struct_0(sK0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_761]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_766,plain,
% 1.99/0.99      ( v1_xboole_0(X0)
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.99/0.99      inference(global_propositional_subsumption,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_762,c_26,c_24,c_73]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_767,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_766]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1358,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X1)
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.99/0.99      | sK1 != X0 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_767,c_20]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1359,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | v1_xboole_0(sK1)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_1358]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1363,plain,
% 1.99/0.99      ( v1_xboole_0(X0)
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1359,c_23]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1364,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/0.99      inference(renaming,[status(thm)],[c_1363]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_1682,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v1_xboole_0(X0)
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | sK1 != sK1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_1364]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2495,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/0.99      | u1_struct_0(sK0) != X0
% 1.99/0.99      | sK1 != sK1 ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_1682,c_814]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2496,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.99/0.99      inference(unflattening,[status(thm)],[c_2495]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_2819,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_2496,c_2480]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_3122,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.99/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.99/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.99/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.99/0.99      inference(resolution_lifted,[status(thm)],[c_2819,c_2464]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4246,plain,
% 1.99/0.99      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/0.99      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.99/0.99      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.99/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
% 1.99/0.99      inference(predicate_to_equality,[status(thm)],[c_3122]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4334,plain,
% 1.99/0.99      ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.99/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/0.99      | r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.99/0.99      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
% 1.99/0.99      inference(light_normalisation,[status(thm)],[c_4246,c_823,c_1112]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4335,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.99/0.99      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/0.99      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
% 1.99/0.99      inference(equality_resolution_simp,[status(thm)],[c_4334]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4340,plain,
% 1.99/0.99      ( r1_waybel_7(sK0,sK1,sK2) = iProver_top ),
% 1.99/0.99      inference(forward_subsumption_resolution,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_4335,c_4294,c_4254,c_4264]) ).
% 1.99/0.99  
% 1.99/0.99  cnf(c_4348,plain,
% 1.99/0.99      ( $false ),
% 1.99/0.99      inference(forward_subsumption_resolution,
% 1.99/0.99                [status(thm)],
% 1.99/0.99                [c_4343,c_4294,c_4254,c_4264,c_4340]) ).
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  ------                               Statistics
% 1.99/0.99  
% 1.99/0.99  ------ General
% 1.99/0.99  
% 1.99/0.99  abstr_ref_over_cycles:                  0
% 1.99/0.99  abstr_ref_under_cycles:                 0
% 1.99/0.99  gc_basic_clause_elim:                   0
% 1.99/0.99  forced_gc_time:                         0
% 1.99/0.99  parsing_time:                           0.011
% 1.99/0.99  unif_index_cands_time:                  0.
% 1.99/0.99  unif_index_add_time:                    0.
% 1.99/0.99  orderings_time:                         0.
% 1.99/0.99  out_proof_time:                         0.021
% 1.99/0.99  total_time:                             0.172
% 1.99/0.99  num_of_symbols:                         56
% 1.99/0.99  num_of_terms:                           1166
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing
% 1.99/0.99  
% 1.99/0.99  num_of_splits:                          0
% 1.99/0.99  num_of_split_atoms:                     0
% 1.99/0.99  num_of_reused_defs:                     0
% 1.99/0.99  num_eq_ax_congr_red:                    4
% 1.99/0.99  num_of_sem_filtered_clauses:            1
% 1.99/0.99  num_of_subtypes:                        0
% 1.99/0.99  monotx_restored_types:                  0
% 1.99/0.99  sat_num_of_epr_types:                   0
% 1.99/0.99  sat_num_of_non_cyclic_types:            0
% 1.99/0.99  sat_guarded_non_collapsed_types:        0
% 1.99/0.99  num_pure_diseq_elim:                    0
% 1.99/0.99  simp_replaced_by:                       0
% 1.99/0.99  res_preprocessed:                       100
% 1.99/0.99  prep_upred:                             0
% 1.99/0.99  prep_unflattend:                        51
% 1.99/0.99  smt_new_axioms:                         0
% 1.99/0.99  pred_elim_cands:                        3
% 1.99/0.99  pred_elim:                              11
% 1.99/0.99  pred_elim_cl:                           9
% 1.99/0.99  pred_elim_cycles:                       20
% 1.99/0.99  merged_defs:                            2
% 1.99/0.99  merged_defs_ncl:                        0
% 1.99/0.99  bin_hyper_res:                          2
% 1.99/0.99  prep_cycles:                            4
% 1.99/0.99  pred_elim_time:                         0.101
% 1.99/0.99  splitting_time:                         0.
% 1.99/0.99  sem_filter_time:                        0.
% 1.99/0.99  monotx_time:                            0.
% 1.99/0.99  subtype_inf_time:                       0.
% 1.99/0.99  
% 1.99/0.99  ------ Problem properties
% 1.99/0.99  
% 1.99/0.99  clauses:                                16
% 1.99/0.99  conjectures:                            2
% 1.99/0.99  epr:                                    0
% 1.99/0.99  horn:                                   12
% 1.99/0.99  ground:                                 14
% 1.99/0.99  unary:                                  7
% 1.99/0.99  binary:                                 1
% 1.99/0.99  lits:                                   57
% 1.99/0.99  lits_eq:                                21
% 1.99/0.99  fd_pure:                                0
% 1.99/0.99  fd_pseudo:                              0
% 1.99/0.99  fd_cond:                                0
% 1.99/0.99  fd_pseudo_cond:                         0
% 1.99/0.99  ac_symbols:                             0
% 1.99/0.99  
% 1.99/0.99  ------ Propositional Solver
% 1.99/0.99  
% 1.99/0.99  prop_solver_calls:                      21
% 1.99/0.99  prop_fast_solver_calls:                 1979
% 1.99/0.99  smt_solver_calls:                       0
% 1.99/0.99  smt_fast_solver_calls:                  0
% 1.99/0.99  prop_num_of_clauses:                    460
% 1.99/0.99  prop_preprocess_simplified:             2264
% 1.99/0.99  prop_fo_subsumed:                       95
% 1.99/0.99  prop_solver_time:                       0.
% 1.99/0.99  smt_solver_time:                        0.
% 1.99/0.99  smt_fast_solver_time:                   0.
% 1.99/0.99  prop_fast_solver_time:                  0.
% 1.99/0.99  prop_unsat_core_time:                   0.
% 1.99/0.99  
% 1.99/0.99  ------ QBF
% 1.99/0.99  
% 1.99/0.99  qbf_q_res:                              0
% 1.99/0.99  qbf_num_tautologies:                    0
% 1.99/0.99  qbf_prep_cycles:                        0
% 1.99/0.99  
% 1.99/0.99  ------ BMC1
% 1.99/0.99  
% 1.99/0.99  bmc1_current_bound:                     -1
% 1.99/0.99  bmc1_last_solved_bound:                 -1
% 1.99/0.99  bmc1_unsat_core_size:                   -1
% 1.99/0.99  bmc1_unsat_core_parents_size:           -1
% 1.99/0.99  bmc1_merge_next_fun:                    0
% 1.99/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.99/0.99  
% 1.99/0.99  ------ Instantiation
% 1.99/0.99  
% 1.99/0.99  inst_num_of_clauses:                    29
% 1.99/0.99  inst_num_in_passive:                    0
% 1.99/0.99  inst_num_in_active:                     0
% 1.99/0.99  inst_num_in_unprocessed:                29
% 1.99/0.99  inst_num_of_loops:                      0
% 1.99/0.99  inst_num_of_learning_restarts:          0
% 1.99/0.99  inst_num_moves_active_passive:          0
% 1.99/0.99  inst_lit_activity:                      0
% 1.99/0.99  inst_lit_activity_moves:                0
% 1.99/0.99  inst_num_tautologies:                   0
% 1.99/0.99  inst_num_prop_implied:                  0
% 1.99/0.99  inst_num_existing_simplified:           0
% 1.99/0.99  inst_num_eq_res_simplified:             0
% 1.99/0.99  inst_num_child_elim:                    0
% 1.99/0.99  inst_num_of_dismatching_blockings:      0
% 1.99/0.99  inst_num_of_non_proper_insts:           0
% 1.99/0.99  inst_num_of_duplicates:                 0
% 1.99/0.99  inst_inst_num_from_inst_to_res:         0
% 1.99/0.99  inst_dismatching_checking_time:         0.
% 1.99/0.99  
% 1.99/0.99  ------ Resolution
% 1.99/0.99  
% 1.99/0.99  res_num_of_clauses:                     0
% 1.99/0.99  res_num_in_passive:                     0
% 1.99/0.99  res_num_in_active:                      0
% 1.99/0.99  res_num_of_loops:                       104
% 1.99/0.99  res_forward_subset_subsumed:            5
% 1.99/0.99  res_backward_subset_subsumed:           0
% 1.99/0.99  res_forward_subsumed:                   12
% 1.99/0.99  res_backward_subsumed:                  12
% 1.99/0.99  res_forward_subsumption_resolution:     2
% 1.99/0.99  res_backward_subsumption_resolution:    0
% 1.99/0.99  res_clause_to_clause_subsumption:       376
% 1.99/0.99  res_orphan_elimination:                 0
% 1.99/0.99  res_tautology_del:                      7
% 1.99/0.99  res_num_eq_res_simplified:              0
% 1.99/0.99  res_num_sel_changes:                    0
% 1.99/0.99  res_moves_from_active_to_pass:          0
% 1.99/0.99  
% 1.99/0.99  ------ Superposition
% 1.99/0.99  
% 1.99/0.99  sup_time_total:                         0.
% 1.99/0.99  sup_time_generating:                    0.
% 1.99/0.99  sup_time_sim_full:                      0.
% 1.99/0.99  sup_time_sim_immed:                     0.
% 1.99/0.99  
% 1.99/0.99  sup_num_of_clauses:                     0
% 1.99/0.99  sup_num_in_active:                      0
% 1.99/0.99  sup_num_in_passive:                     0
% 1.99/0.99  sup_num_of_loops:                       0
% 1.99/0.99  sup_fw_superposition:                   0
% 1.99/0.99  sup_bw_superposition:                   0
% 1.99/0.99  sup_immediate_simplified:               0
% 1.99/0.99  sup_given_eliminated:                   0
% 1.99/0.99  comparisons_done:                       0
% 1.99/0.99  comparisons_avoided:                    0
% 1.99/0.99  
% 1.99/0.99  ------ Simplifications
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  sim_fw_subset_subsumed:                 0
% 1.99/0.99  sim_bw_subset_subsumed:                 0
% 1.99/0.99  sim_fw_subsumed:                        1
% 1.99/0.99  sim_bw_subsumed:                        1
% 1.99/0.99  sim_fw_subsumption_res:                 14
% 1.99/0.99  sim_bw_subsumption_res:                 0
% 1.99/0.99  sim_tautology_del:                      0
% 1.99/0.99  sim_eq_tautology_del:                   0
% 1.99/0.99  sim_eq_res_simp:                        4
% 1.99/0.99  sim_fw_demodulated:                     1
% 1.99/0.99  sim_bw_demodulated:                     0
% 1.99/0.99  sim_light_normalised:                   10
% 1.99/0.99  sim_joinable_taut:                      0
% 1.99/0.99  sim_joinable_simp:                      0
% 1.99/0.99  sim_ac_normalised:                      0
% 1.99/0.99  sim_smt_subsumption:                    0
% 1.99/0.99  
%------------------------------------------------------------------------------
