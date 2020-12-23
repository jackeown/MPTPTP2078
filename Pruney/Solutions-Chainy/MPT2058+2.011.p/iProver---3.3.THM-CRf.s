%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:16 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  243 (1969 expanded)
%              Number of clauses        :  154 ( 430 expanded)
%              Number of leaves         :   19 ( 539 expanded)
%              Depth                    :   36
%              Number of atoms          : 1508 (17119 expanded)
%              Number of equality atoms :  244 ( 502 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f51,f50,f49])).

fof(f80,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f80,f63])).

fof(f11,axiom,(
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

fof(f20,plain,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
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
    inference(definition_unfolding,[],[f67,f63,f63,f63])).

fof(f85,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f75,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f81,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f81,f63])).

fof(f78,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
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
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f18])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f88,plain,(
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
    inference(definition_unfolding,[],[f69,f63,f63,f63])).

fof(f13,axiom,(
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

fof(f19,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
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
    inference(definition_unfolding,[],[f71,f63,f63,f63,f63])).

fof(f79,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f96,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f79,f63])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
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
    inference(definition_unfolding,[],[f66,f63,f63,f63])).

fof(f15,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f74,f63,f63,f63,f63])).

fof(f82,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f52])).

fof(f93,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f82,f63])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f84,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f64,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_26,negated_conjecture,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_12,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_21,negated_conjecture,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_232,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_570,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_571,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_575,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_31,c_29])).

cnf(c_1063,plain,
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
    inference(resolution_lifted,[status(thm)],[c_232,c_575])).

cnf(c_1064,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_1063])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1066,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1064,c_23])).

cnf(c_1067,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_1066])).

cnf(c_1103,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_1067])).

cnf(c_1104,plain,
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
    inference(unflattening,[status(thm)],[c_1103])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_93,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1108,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1104,c_31,c_29,c_93])).

cnf(c_1109,plain,
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
    inference(renaming,[status(thm)],[c_1108])).

cnf(c_25,negated_conjecture,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1700,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1109,c_25])).

cnf(c_1701,plain,
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
    inference(unflattening,[status(thm)],[c_1700])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1705,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1701,c_28])).

cnf(c_1706,plain,
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
    inference(renaming,[status(thm)],[c_1705])).

cnf(c_2049,plain,
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
    inference(resolution_lifted,[status(thm)],[c_26,c_1706])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_620,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_29])).

cnf(c_621,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_1212,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_621])).

cnf(c_1213,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_1212])).

cnf(c_90,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1215,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1213,c_31,c_29,c_90,c_93])).

cnf(c_2753,plain,
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
    inference(resolution_lifted,[status(thm)],[c_2049,c_1215])).

cnf(c_2754,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2753])).

cnf(c_14,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1230,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_621])).

cnf(c_1231,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1230])).

cnf(c_1235,plain,
    ( v4_orders_2(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1231,c_31])).

cnf(c_1236,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1235])).

cnf(c_1625,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1236,c_25])).

cnf(c_1626,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1625])).

cnf(c_1630,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1626,c_28])).

cnf(c_1631,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1630])).

cnf(c_2125,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1631])).

cnf(c_2706,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_2125,c_1215])).

cnf(c_2707,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v4_orders_2(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2706])).

cnf(c_3007,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_2754,c_2707])).

cnf(c_16,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_27,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_439,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_440,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_444,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_28])).

cnf(c_445,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_444])).

cnf(c_1296,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_445,c_621])).

cnf(c_1297,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1296])).

cnf(c_1301,plain,
    ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1297,c_31])).

cnf(c_1302,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1301])).

cnf(c_1745,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_1302])).

cnf(c_2023,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1745])).

cnf(c_2784,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_2023,c_1215])).

cnf(c_2785,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v7_waybel_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_2784])).

cnf(c_3268,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_3007,c_2785])).

cnf(c_13,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1263,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_621])).

cnf(c_1264,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1263])).

cnf(c_1268,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1264,c_31])).

cnf(c_1269,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1268])).

cnf(c_1595,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1269,c_25])).

cnf(c_1596,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1595])).

cnf(c_1600,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1596,c_28])).

cnf(c_1601,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1600])).

cnf(c_2148,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1601])).

cnf(c_2690,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_2148,c_1215])).

cnf(c_2691,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v2_struct_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2690])).

cnf(c_3571,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_3268,c_2691])).

cnf(c_3929,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
    | r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3571])).

cnf(c_20,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_478,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_479,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_483,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_28])).

cnf(c_484,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_1201,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_484,c_621])).

cnf(c_1202,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_1201])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1204,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1202,c_31,c_26,c_25,c_24])).

cnf(c_3678,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_1204])).

cnf(c_4004,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3929,c_3678])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3937,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3944,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3937,c_0])).

cnf(c_22,negated_conjecture,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_234,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_537,plain,
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
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_538,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_542,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_31,c_29])).

cnf(c_1037,plain,
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
    inference(resolution_lifted,[status(thm)],[c_234,c_542])).

cnf(c_1038,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_1037])).

cnf(c_1040,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,sK1,sK2)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1038,c_23])).

cnf(c_1041,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_1040])).

cnf(c_1151,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_1041])).

cnf(c_1152,plain,
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
    inference(unflattening,[status(thm)],[c_1151])).

cnf(c_1156,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1152,c_31,c_29,c_93])).

cnf(c_1157,plain,
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
    inference(renaming,[status(thm)],[c_1156])).

cnf(c_1655,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1157,c_25])).

cnf(c_1656,plain,
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
    inference(unflattening,[status(thm)],[c_1655])).

cnf(c_1660,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1656,c_28])).

cnf(c_1661,plain,
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
    inference(renaming,[status(thm)],[c_1660])).

cnf(c_2087,plain,
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
    inference(resolution_lifted,[status(thm)],[c_26,c_1661])).

cnf(c_2722,plain,
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
    inference(resolution_lifted,[status(thm)],[c_2087,c_1215])).

cnf(c_2723,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2722])).

cnf(c_3034,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_2723,c_2707])).

cnf(c_3241,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_3034,c_2785])).

cnf(c_3595,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_3241,c_2691])).

cnf(c_3928,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3595])).

cnf(c_3991,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3928,c_3678])).

cnf(c_3998,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3991,c_3944])).

cnf(c_4011,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4004,c_3944,c_3998])).

cnf(c_5,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2
    | k2_pre_topc(X1,X0) = X0
    | k2_struct_0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_415,plain,
    ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_2,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_419,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_3,c_2])).

cnf(c_529,plain,
    ( ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_419,c_30])).

cnf(c_530,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_96,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_417,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_532,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_30,c_29,c_93,c_96,c_417])).

cnf(c_8,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_672,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_673,plain,
    ( v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_672])).

cnf(c_11,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_627,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_628,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = u1_struct_0(sK0)
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
    inference(resolution,[status(thm)],[c_673,c_628])).

cnf(c_3934,plain,
    ( k2_pre_topc(sK0,X0) = u1_struct_0(sK0)
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_4204,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = u1_struct_0(sK0)
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_532,c_3934])).

cnf(c_4205,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4204,c_532])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_92,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_94,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_struct_0(sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_95,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_97,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_struct_0(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_4208,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4205,c_34,c_94,c_97])).

cnf(c_4374,plain,
    ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4011,c_4208])).

cnf(c_4375,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4374])).

cnf(c_3935,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4377,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4375,c_3935])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.03/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.03/0.99  
% 2.03/0.99  ------  iProver source info
% 2.03/0.99  
% 2.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.03/0.99  git: non_committed_changes: false
% 2.03/0.99  git: last_make_outside_of_git: false
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     num_symb
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       true
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/0.99  --sup_to_prop_solver                    passive
% 2.03/0.99  --sup_prop_simpl_new                    true
% 2.03/0.99  --sup_prop_simpl_given                  true
% 2.03/0.99  --sup_fun_splitting                     false
% 2.03/0.99  --sup_smt_interval                      50000
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Simplification Setup
% 2.03/0.99  
% 2.03/0.99  --sup_indices_passive                   []
% 2.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_full_bw                           [BwDemod]
% 2.03/0.99  --sup_immed_triv                        [TrivRules]
% 2.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_immed_bw_main                     []
% 2.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  
% 2.03/0.99  ------ Combination Options
% 2.03/0.99  
% 2.03/0.99  --comb_res_mult                         3
% 2.03/0.99  --comb_sup_mult                         2
% 2.03/0.99  --comb_inst_mult                        10
% 2.03/0.99  
% 2.03/0.99  ------ Debug Options
% 2.03/0.99  
% 2.03/0.99  --dbg_backtrace                         false
% 2.03/0.99  --dbg_dump_prop_clauses                 false
% 2.03/0.99  --dbg_dump_prop_clauses_file            -
% 2.03/0.99  --dbg_out_stat                          false
% 2.03/0.99  ------ Parsing...
% 2.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 13 0s  sf_e  pe_s  pe_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.03/0.99  ------ Proving...
% 2.03/0.99  ------ Problem Properties 
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  clauses                                 13
% 2.03/0.99  conjectures                             2
% 2.03/0.99  EPR                                     0
% 2.03/0.99  Horn                                    11
% 2.03/0.99  unary                                   7
% 2.03/0.99  binary                                  0
% 2.03/0.99  lits                                    41
% 2.03/0.99  lits eq                                 19
% 2.03/0.99  fd_pure                                 0
% 2.03/0.99  fd_pseudo                               0
% 2.03/0.99  fd_cond                                 0
% 2.03/0.99  fd_pseudo_cond                          0
% 2.03/0.99  AC symbols                              0
% 2.03/0.99  
% 2.03/0.99  ------ Schedule dynamic 5 is on 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  Current options:
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     none
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       false
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/0.99  --sup_to_prop_solver                    passive
% 2.03/0.99  --sup_prop_simpl_new                    true
% 2.03/0.99  --sup_prop_simpl_given                  true
% 2.03/0.99  --sup_fun_splitting                     false
% 2.03/0.99  --sup_smt_interval                      50000
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Simplification Setup
% 2.03/0.99  
% 2.03/0.99  --sup_indices_passive                   []
% 2.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_full_bw                           [BwDemod]
% 2.03/0.99  --sup_immed_triv                        [TrivRules]
% 2.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_immed_bw_main                     []
% 2.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  
% 2.03/0.99  ------ Combination Options
% 2.03/0.99  
% 2.03/0.99  --comb_res_mult                         3
% 2.03/0.99  --comb_sup_mult                         2
% 2.03/0.99  --comb_inst_mult                        10
% 2.03/0.99  
% 2.03/0.99  ------ Debug Options
% 2.03/0.99  
% 2.03/0.99  --dbg_backtrace                         false
% 2.03/0.99  --dbg_dump_prop_clauses                 false
% 2.03/0.99  --dbg_dump_prop_clauses_file            -
% 2.03/0.99  --dbg_out_stat                          false
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  ------ Proving...
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  % SZS status Theorem for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99   Resolution empty clause
% 2.03/0.99  
% 2.03/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  fof(f16,conjecture,(
% 2.03/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f17,negated_conjecture,(
% 2.03/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.03/0.99    inference(negated_conjecture,[],[f16])).
% 2.03/0.99  
% 2.03/0.99  fof(f42,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f17])).
% 2.03/0.99  
% 2.03/0.99  fof(f43,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f42])).
% 2.03/0.99  
% 2.03/0.99  fof(f47,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.03/0.99    inference(nnf_transformation,[],[f43])).
% 2.03/0.99  
% 2.03/0.99  fof(f48,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f47])).
% 2.03/0.99  
% 2.03/0.99  fof(f51,plain,(
% 2.03/0.99    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & (r1_waybel_7(X0,X1,sK2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f50,plain,(
% 2.03/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & (r1_waybel_7(X0,sK1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK1))) )),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f49,plain,(
% 2.03/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.03/0.99    introduced(choice_axiom,[])).
% 2.03/0.99  
% 2.03/0.99  fof(f52,plain,(
% 2.03/0.99    (((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.03/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f51,f50,f49])).
% 2.03/0.99  
% 2.03/0.99  fof(f80,plain,(
% 2.03/0.99    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 2.03/0.99    inference(cnf_transformation,[],[f52])).
% 2.03/0.99  
% 2.03/0.99  fof(f9,axiom,(
% 2.03/0.99    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f63,plain,(
% 2.03/0.99    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f9])).
% 2.03/0.99  
% 2.03/0.99  fof(f95,plain,(
% 2.03/0.99    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 2.03/0.99    inference(definition_unfolding,[],[f80,f63])).
% 2.03/0.99  
% 2.03/0.99  fof(f11,axiom,(
% 2.03/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f20,plain,(
% 2.03/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.03/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.03/0.99  
% 2.03/0.99  fof(f32,plain,(
% 2.03/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f20])).
% 2.03/0.99  
% 2.03/0.99  fof(f33,plain,(
% 2.03/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f32])).
% 2.03/0.99  
% 2.03/0.99  fof(f67,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f33])).
% 2.03/0.99  
% 2.03/0.99  fof(f86,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f67,f63,f63,f63])).
% 2.03/0.99  
% 2.03/0.99  fof(f85,plain,(
% 2.03/0.99    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 2.03/0.99    inference(cnf_transformation,[],[f52])).
% 2.03/0.99  
% 2.03/0.99  fof(f14,axiom,(
% 2.03/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f38,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f14])).
% 2.03/0.99  
% 2.03/0.99  fof(f39,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f38])).
% 2.03/0.99  
% 2.03/0.99  fof(f46,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.99    inference(nnf_transformation,[],[f39])).
% 2.03/0.99  
% 2.03/0.99  fof(f73,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f46])).
% 2.03/0.99  
% 2.03/0.99  fof(f76,plain,(
% 2.03/0.99    v2_pre_topc(sK0)),
% 2.03/0.99    inference(cnf_transformation,[],[f52])).
% 2.03/0.99  
% 2.03/0.99  fof(f75,plain,(
% 2.03/0.99    ~v2_struct_0(sK0)),
% 2.03/0.99    inference(cnf_transformation,[],[f52])).
% 2.03/0.99  
% 2.03/0.99  fof(f77,plain,(
% 2.03/0.99    l1_pre_topc(sK0)),
% 2.03/0.99    inference(cnf_transformation,[],[f52])).
% 2.03/0.99  
% 2.03/0.99  fof(f83,plain,(
% 2.03/0.99    m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.03/0.99    inference(cnf_transformation,[],[f52])).
% 2.03/0.99  
% 2.03/0.99  fof(f4,axiom,(
% 2.03/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f23,plain,(
% 2.03/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f4])).
% 2.03/0.99  
% 2.03/0.99  fof(f56,plain,(
% 2.03/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f23])).
% 2.03/0.99  
% 2.03/0.99  fof(f81,plain,(
% 2.03/0.99    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 2.03/0.99    inference(cnf_transformation,[],[f52])).
% 2.03/0.99  
% 2.03/0.99  fof(f94,plain,(
% 2.03/0.99    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 2.03/0.99    inference(definition_unfolding,[],[f81,f63])).
% 2.03/0.99  
% 2.03/0.99  fof(f78,plain,(
% 2.03/0.99    ~v1_xboole_0(sK1)),
% 2.03/0.99    inference(cnf_transformation,[],[f52])).
% 2.03/0.99  
% 2.03/0.99  fof(f5,axiom,(
% 2.03/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f24,plain,(
% 2.03/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f5])).
% 2.03/0.99  
% 2.03/0.99  fof(f25,plain,(
% 2.03/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f24])).
% 2.03/0.99  
% 2.03/0.99  fof(f57,plain,(
% 2.03/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f25])).
% 2.03/0.99  
% 2.03/0.99  fof(f12,axiom,(
% 2.03/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f18,plain,(
% 2.03/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.03/0.99    inference(pure_predicate_removal,[],[f12])).
% 2.03/0.99  
% 2.03/0.99  fof(f21,plain,(
% 2.03/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.03/0.99    inference(pure_predicate_removal,[],[f18])).
% 2.03/0.99  
% 2.03/0.99  fof(f34,plain,(
% 2.03/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f21])).
% 2.03/0.99  
% 2.03/0.99  fof(f35,plain,(
% 2.03/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f34])).
% 2.03/0.99  
% 2.03/0.99  fof(f69,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f35])).
% 2.03/0.99  
% 2.03/0.99  fof(f88,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f69,f63,f63,f63])).
% 2.03/0.99  
% 2.03/0.99  fof(f13,axiom,(
% 2.03/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f19,plain,(
% 2.03/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.03/0.99    inference(pure_predicate_removal,[],[f13])).
% 2.03/0.99  
% 2.03/0.99  fof(f36,plain,(
% 2.03/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f19])).
% 2.03/0.99  
% 2.03/0.99  fof(f37,plain,(
% 2.03/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f36])).
% 2.03/0.99  
% 2.03/0.99  fof(f71,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f37])).
% 2.03/0.99  
% 2.03/0.99  fof(f90,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f71,f63,f63,f63,f63])).
% 2.03/0.99  
% 2.03/0.99  fof(f79,plain,(
% 2.03/0.99    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 2.03/0.99    inference(cnf_transformation,[],[f52])).
% 2.03/0.99  
% 2.03/0.99  fof(f96,plain,(
% 2.03/0.99    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 2.03/0.99    inference(definition_unfolding,[],[f79,f63])).
% 2.03/0.99  
% 2.03/0.99  fof(f66,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f33])).
% 2.03/0.99  
% 2.03/0.99  fof(f87,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f66,f63,f63,f63])).
% 2.03/0.99  
% 2.03/0.99  fof(f15,axiom,(
% 2.03/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f40,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f15])).
% 2.03/0.99  
% 2.03/0.99  fof(f41,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.03/0.99    inference(flattening,[],[f40])).
% 2.03/0.99  
% 2.03/0.99  fof(f74,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f41])).
% 2.03/0.99  
% 2.03/0.99  fof(f92,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(definition_unfolding,[],[f74,f63,f63,f63,f63])).
% 2.03/0.99  
% 2.03/0.99  fof(f82,plain,(
% 2.03/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 2.03/0.99    inference(cnf_transformation,[],[f52])).
% 2.03/0.99  
% 2.03/0.99  fof(f93,plain,(
% 2.03/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 2.03/0.99    inference(definition_unfolding,[],[f82,f63])).
% 2.03/0.99  
% 2.03/0.99  fof(f2,axiom,(
% 2.03/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f54,plain,(
% 2.03/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.03/0.99    inference(cnf_transformation,[],[f2])).
% 2.03/0.99  
% 2.03/0.99  fof(f1,axiom,(
% 2.03/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f53,plain,(
% 2.03/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.03/0.99    inference(cnf_transformation,[],[f1])).
% 2.03/0.99  
% 2.03/0.99  fof(f84,plain,(
% 2.03/0.99    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 2.03/0.99    inference(cnf_transformation,[],[f52])).
% 2.03/0.99  
% 2.03/0.99  fof(f72,plain,(
% 2.03/0.99    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f46])).
% 2.03/0.99  
% 2.03/0.99  fof(f6,axiom,(
% 2.03/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f26,plain,(
% 2.03/0.99    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.03/0.99    inference(ennf_transformation,[],[f6])).
% 2.03/0.99  
% 2.03/0.99  fof(f27,plain,(
% 2.03/0.99    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.99    inference(flattening,[],[f26])).
% 2.03/0.99  
% 2.03/0.99  fof(f58,plain,(
% 2.03/0.99    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f27])).
% 2.03/0.99  
% 2.03/0.99  fof(f7,axiom,(
% 2.03/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f28,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f7])).
% 2.03/0.99  
% 2.03/0.99  fof(f29,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(flattening,[],[f28])).
% 2.03/0.99  
% 2.03/0.99  fof(f59,plain,(
% 2.03/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f29])).
% 2.03/0.99  
% 2.03/0.99  fof(f3,axiom,(
% 2.03/0.99    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f22,plain,(
% 2.03/0.99    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f3])).
% 2.03/0.99  
% 2.03/0.99  fof(f55,plain,(
% 2.03/0.99    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f22])).
% 2.03/0.99  
% 2.03/0.99  fof(f8,axiom,(
% 2.03/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f30,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f8])).
% 2.03/0.99  
% 2.03/0.99  fof(f44,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(nnf_transformation,[],[f30])).
% 2.03/0.99  
% 2.03/0.99  fof(f62,plain,(
% 2.03/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f44])).
% 2.03/0.99  
% 2.03/0.99  fof(f10,axiom,(
% 2.03/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.03/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/0.99  
% 2.03/0.99  fof(f31,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(ennf_transformation,[],[f10])).
% 2.03/0.99  
% 2.03/0.99  fof(f45,plain,(
% 2.03/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.99    inference(nnf_transformation,[],[f31])).
% 2.03/0.99  
% 2.03/0.99  fof(f64,plain,(
% 2.03/0.99    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.99    inference(cnf_transformation,[],[f45])).
% 2.03/0.99  
% 2.03/0.99  cnf(c_26,negated_conjecture,
% 2.03/0.99      ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.03/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_12,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | v2_struct_0(X2)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | ~ l1_struct_0(X2) ),
% 2.03/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_21,negated_conjecture,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 2.03/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_232,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 2.03/0.99      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_18,plain,
% 2.03/0.99      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.03/0.99      | r3_waybel_9(X0,X1,X2)
% 2.03/0.99      | ~ l1_waybel_0(X1,X0)
% 2.03/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.03/0.99      | ~ v7_waybel_0(X1)
% 2.03/0.99      | ~ v4_orders_2(X1)
% 2.03/0.99      | ~ v2_pre_topc(X0)
% 2.03/0.99      | v2_struct_0(X0)
% 2.03/0.99      | v2_struct_0(X1)
% 2.03/0.99      | ~ l1_pre_topc(X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_30,negated_conjecture,
% 2.03/0.99      ( v2_pre_topc(sK0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_570,plain,
% 2.03/0.99      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.03/0.99      | r3_waybel_9(X0,X1,X2)
% 2.03/0.99      | ~ l1_waybel_0(X1,X0)
% 2.03/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.03/0.99      | ~ v7_waybel_0(X1)
% 2.03/0.99      | ~ v4_orders_2(X1)
% 2.03/0.99      | v2_struct_0(X0)
% 2.03/0.99      | v2_struct_0(X1)
% 2.03/0.99      | ~ l1_pre_topc(X0)
% 2.03/0.99      | sK0 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_571,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.03/0.99      | r3_waybel_9(sK0,X0,X1)
% 2.03/0.99      | ~ l1_waybel_0(X0,sK0)
% 2.03/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.03/0.99      | ~ v7_waybel_0(X0)
% 2.03/0.99      | ~ v4_orders_2(X0)
% 2.03/0.99      | v2_struct_0(X0)
% 2.03/0.99      | v2_struct_0(sK0)
% 2.03/0.99      | ~ l1_pre_topc(sK0) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_570]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_31,negated_conjecture,
% 2.03/0.99      ( ~ v2_struct_0(sK0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_29,negated_conjecture,
% 2.03/0.99      ( l1_pre_topc(sK0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_575,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.03/0.99      | r3_waybel_9(sK0,X0,X1)
% 2.03/0.99      | ~ l1_waybel_0(X0,sK0)
% 2.03/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.03/0.99      | ~ v7_waybel_0(X0)
% 2.03/0.99      | ~ v4_orders_2(X0)
% 2.03/0.99      | v2_struct_0(X0) ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_571,c_31,c_29]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1063,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ l1_waybel_0(X0,sK0)
% 2.03/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.03/0.99      | ~ v7_waybel_0(X0)
% 2.03/0.99      | ~ v4_orders_2(X0)
% 2.03/0.99      | v2_struct_0(X0)
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 2.03/0.99      | sK2 != X1
% 2.03/0.99      | sK0 != sK0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_232,c_575]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1064,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.03/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_1063]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_23,negated_conjecture,
% 2.03/0.99      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 2.03/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1066,plain,
% 2.03/0.99      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.03/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1064,c_23]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1067,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_1066]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1103,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(X2)
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | ~ l1_struct_0(X2)
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 2.03/0.99      | sK0 != X2 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_1067]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1104,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(sK0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | ~ l1_struct_0(sK0)
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_1103]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3,plain,
% 2.03/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_93,plain,
% 2.03/0.99      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1108,plain,
% 2.03/0.99      ( v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_1104,c_31,c_29,c_93]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1109,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_1108]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_25,negated_conjecture,
% 2.03/0.99      ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.03/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1700,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 2.03/0.99      | sK1 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_1109,c_25]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1701,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(sK1)
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_1700]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_28,negated_conjecture,
% 2.03/0.99      ( ~ v1_xboole_0(sK1) ),
% 2.03/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1705,plain,
% 2.03/0.99      ( v1_xboole_0(X0)
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1701,c_28]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1706,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_1705]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2049,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | sK1 != sK1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_1706]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_4,plain,
% 2.03/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 2.03/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_620,plain,
% 2.03/0.99      ( l1_struct_0(X0) | sK0 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_29]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_621,plain,
% 2.03/0.99      ( l1_struct_0(sK0) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_620]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1212,plain,
% 2.03/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK0 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_621]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1213,plain,
% 2.03/0.99      ( v2_struct_0(sK0) | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_1212]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_90,plain,
% 2.03/0.99      ( v2_struct_0(sK0)
% 2.03/0.99      | ~ v1_xboole_0(u1_struct_0(sK0))
% 2.03/0.99      | ~ l1_struct_0(sK0) ),
% 2.03/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1215,plain,
% 2.03/0.99      ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 2.03/0.99      inference(global_propositional_subsumption,
% 2.03/0.99                [status(thm)],
% 2.03/0.99                [c_1213,c_31,c_29,c_90,c_93]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2753,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | u1_struct_0(sK0) != X0
% 2.03/0.99      | sK1 != sK1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_2049,c_1215]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2754,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_2753]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_14,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.03/0.99      | v2_struct_0(X2)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | ~ l1_struct_0(X2) ),
% 2.03/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1230,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.03/0.99      | v2_struct_0(X2)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | sK0 != X2 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_621]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1231,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 2.03/0.99      | v2_struct_0(sK0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_1230]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1235,plain,
% 2.03/0.99      ( v4_orders_2(k3_yellow19(sK0,X1,X0))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0) ),
% 2.03/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1231,c_31]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1236,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_1235]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1625,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 2.03/0.99      | sK1 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_1236,c_25]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1626,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(sK1)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_1625]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1630,plain,
% 2.03/0.99      ( v1_xboole_0(X0)
% 2.03/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1626,c_28]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1631,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_1630]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2125,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | sK1 != sK1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_1631]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2706,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | u1_struct_0(sK0) != X0
% 2.03/0.99      | sK1 != sK1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_2125,c_1215]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2707,plain,
% 2.03/0.99      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 2.03/0.99      | v4_orders_2(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_2706]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3007,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 2.03/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_2754,c_2707]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_16,plain,
% 2.03/0.99      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.03/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.03/0.99      | v2_struct_0(X2)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | ~ l1_struct_0(X2) ),
% 2.03/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_27,negated_conjecture,
% 2.03/0.99      ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
% 2.03/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_439,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.03/0.99      | v2_struct_0(X2)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | ~ l1_struct_0(X2)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | sK1 != X0 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_440,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 2.03/0.99      | v2_struct_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | v1_xboole_0(sK1)
% 2.03/0.99      | ~ l1_struct_0(X1)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_439]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_444,plain,
% 2.03/0.99      ( v1_xboole_0(X0)
% 2.03/0.99      | v2_struct_0(X1)
% 2.03/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ l1_struct_0(X1)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.03/0.99      inference(global_propositional_subsumption,[status(thm)],[c_440,c_28]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_445,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 2.03/0.99      | v2_struct_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | ~ l1_struct_0(X1)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_444]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1296,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 2.03/0.99      | v2_struct_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | sK0 != X1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_445,c_621]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1297,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.03/0.99      | v2_struct_0(sK0)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_1296]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1301,plain,
% 2.03/0.99      ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.03/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1297,c_31]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1302,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.03/0.99      inference(renaming,[status(thm)],[c_1301]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1745,plain,
% 2.03/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | sK1 != sK1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_1302]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2023,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | sK1 != sK1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_1745]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2784,plain,
% 2.03/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.03/0.99      | u1_struct_0(sK0) != X0
% 2.03/0.99      | sK1 != sK1 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_2023,c_1215]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_2785,plain,
% 2.03/0.99      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 2.03/0.99      | v7_waybel_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 2.03/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_2784]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_3268,plain,
% 2.03/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 2.03/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.03/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_3007,c_2785]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_13,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | v2_struct_0(X2)
% 2.03/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | ~ l1_struct_0(X2) ),
% 2.03/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1263,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | v2_struct_0(X2)
% 2.03/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0)
% 2.03/0.99      | sK0 != X2 ),
% 2.03/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_621]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1264,plain,
% 2.03/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 2.03/0.99      | v2_struct_0(sK0)
% 2.03/0.99      | v1_xboole_0(X1)
% 2.03/0.99      | v1_xboole_0(X0) ),
% 2.03/0.99      inference(unflattening,[status(thm)],[c_1263]) ).
% 2.03/0.99  
% 2.03/0.99  cnf(c_1268,plain,
% 2.03/1.00      ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 2.03/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | v1_xboole_0(X1)
% 2.03/1.00      | v1_xboole_0(X0) ),
% 2.03/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1264,c_31]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1269,plain,
% 2.03/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 2.03/1.00      | v1_xboole_0(X1)
% 2.03/1.00      | v1_xboole_0(X0) ),
% 2.03/1.00      inference(renaming,[status(thm)],[c_1268]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1595,plain,
% 2.03/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 2.03/1.00      | v1_xboole_0(X1)
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 2.03/1.00      | sK1 != X0 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_1269,c_25]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1596,plain,
% 2.03/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | v1_xboole_0(sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_1595]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1600,plain,
% 2.03/1.00      ( v1_xboole_0(X0)
% 2.03/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1596,c_28]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1601,plain,
% 2.03/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/1.00      inference(renaming,[status(thm)],[c_1600]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2148,plain,
% 2.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.03/1.00      | sK1 != sK1 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_1601]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2690,plain,
% 2.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.03/1.00      | u1_struct_0(sK0) != X0
% 2.03/1.00      | sK1 != sK1 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_2148,c_1215]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2691,plain,
% 2.03/1.00      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 2.03/1.00      | ~ v2_struct_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_2690]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3571,plain,
% 2.03/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 2.03/1.00      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_3268,c_2691]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3929,plain,
% 2.03/1.00      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.03/1.00      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 2.03/1.00      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.03/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_3571]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_20,plain,
% 2.03/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 2.03/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.03/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.03/1.00      | v2_struct_0(X1)
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | ~ l1_struct_0(X1)
% 2.03/1.00      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 2.03/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_478,plain,
% 2.03/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.03/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.03/1.00      | v2_struct_0(X1)
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | ~ l1_struct_0(X1)
% 2.03/1.00      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.03/1.00      | sK1 != X0 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_479,plain,
% 2.03/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.03/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.03/1.00      | v2_struct_0(X0)
% 2.03/1.00      | v1_xboole_0(sK1)
% 2.03/1.00      | ~ l1_struct_0(X0)
% 2.03/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_478]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_483,plain,
% 2.03/1.00      ( v2_struct_0(X0)
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.03/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.03/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.03/1.00      | ~ l1_struct_0(X0)
% 2.03/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.03/1.00      inference(global_propositional_subsumption,[status(thm)],[c_479,c_28]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_484,plain,
% 2.03/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.03/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.03/1.00      | v2_struct_0(X0)
% 2.03/1.00      | ~ l1_struct_0(X0)
% 2.03/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.03/1.00      inference(renaming,[status(thm)],[c_483]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1201,plain,
% 2.03/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.03/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.03/1.00      | v2_struct_0(X0)
% 2.03/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.03/1.00      | sK0 != X0 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_484,c_621]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1202,plain,
% 2.03/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.03/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 2.03/1.00      | v2_struct_0(sK0)
% 2.03/1.00      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_1201]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_24,negated_conjecture,
% 2.03/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
% 2.03/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1204,plain,
% 2.03/1.00      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_1202,c_31,c_26,c_25,c_24]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3678,plain,
% 2.03/1.00      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 2.03/1.00      inference(equality_resolution_simp,[status(thm)],[c_1204]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_4004,plain,
% 2.03/1.00      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 2.03/1.00      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.03/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 2.03/1.00      inference(light_normalisation,[status(thm)],[c_3929,c_3678]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1,plain,
% 2.03/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.03/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3937,plain,
% 2.03/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_0,plain,
% 2.03/1.00      ( k2_subset_1(X0) = X0 ),
% 2.03/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3944,plain,
% 2.03/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.03/1.00      inference(light_normalisation,[status(thm)],[c_3937,c_0]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_22,negated_conjecture,
% 2.03/1.00      ( r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 2.03/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_234,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 2.03/1.00      inference(prop_impl,[status(thm)],[c_22]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_19,plain,
% 2.03/1.00      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.03/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 2.03/1.00      | ~ l1_waybel_0(X1,X0)
% 2.03/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.03/1.00      | ~ v7_waybel_0(X1)
% 2.03/1.00      | ~ v4_orders_2(X1)
% 2.03/1.00      | ~ v2_pre_topc(X0)
% 2.03/1.00      | v2_struct_0(X0)
% 2.03/1.00      | v2_struct_0(X1)
% 2.03/1.00      | ~ l1_pre_topc(X0) ),
% 2.03/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_537,plain,
% 2.03/1.00      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.03/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 2.03/1.00      | ~ l1_waybel_0(X1,X0)
% 2.03/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.03/1.00      | ~ v7_waybel_0(X1)
% 2.03/1.00      | ~ v4_orders_2(X1)
% 2.03/1.00      | v2_struct_0(X0)
% 2.03/1.00      | v2_struct_0(X1)
% 2.03/1.00      | ~ l1_pre_topc(X0)
% 2.03/1.00      | sK0 != X0 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_538,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.03/1.00      | ~ r3_waybel_9(sK0,X0,X1)
% 2.03/1.00      | ~ l1_waybel_0(X0,sK0)
% 2.03/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.03/1.00      | ~ v7_waybel_0(X0)
% 2.03/1.00      | ~ v4_orders_2(X0)
% 2.03/1.00      | v2_struct_0(X0)
% 2.03/1.00      | v2_struct_0(sK0)
% 2.03/1.00      | ~ l1_pre_topc(sK0) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_537]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_542,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.03/1.00      | ~ r3_waybel_9(sK0,X0,X1)
% 2.03/1.00      | ~ l1_waybel_0(X0,sK0)
% 2.03/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.03/1.00      | ~ v7_waybel_0(X0)
% 2.03/1.00      | ~ v4_orders_2(X0)
% 2.03/1.00      | v2_struct_0(X0) ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_538,c_31,c_29]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1037,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ l1_waybel_0(X0,sK0)
% 2.03/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.03/1.00      | ~ v7_waybel_0(X0)
% 2.03/1.00      | ~ v4_orders_2(X0)
% 2.03/1.00      | v2_struct_0(X0)
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 2.03/1.00      | sK2 != X1
% 2.03/1.00      | sK0 != sK0 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_234,c_542]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1038,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.03/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_1037]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1040,plain,
% 2.03/1.00      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.03/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1038,c_23]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1041,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.03/1.00      inference(renaming,[status(thm)],[c_1040]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1151,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(X2)
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v1_xboole_0(X1)
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | ~ l1_struct_0(X2)
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 2.03/1.00      | sK0 != X2 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_1041]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1152,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(sK0)
% 2.03/1.00      | v1_xboole_0(X1)
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | ~ l1_struct_0(sK0)
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_1151]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1156,plain,
% 2.03/1.00      ( v1_xboole_0(X0)
% 2.03/1.00      | v1_xboole_0(X1)
% 2.03/1.00      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_1152,c_31,c_29,c_93]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1157,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v1_xboole_0(X1)
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 2.03/1.00      inference(renaming,[status(thm)],[c_1156]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1655,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.03/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v1_xboole_0(X1)
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 2.03/1.00      | sK1 != X0 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_1157,c_25]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1656,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | v1_xboole_0(sK1)
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_1655]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1660,plain,
% 2.03/1.00      ( v1_xboole_0(X0)
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1656,c_28]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1661,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.03/1.00      inference(renaming,[status(thm)],[c_1660]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2087,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v1_xboole_0(X0)
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.03/1.00      | sK1 != sK1 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_1661]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2722,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.03/1.00      | u1_struct_0(sK0) != X0
% 2.03/1.00      | sK1 != sK1 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_2087,c_1215]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2723,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_2722]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3034,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 2.03/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_2723,c_2707]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3241,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 2.03/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.03/1.00      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_3034,c_2785]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3595,plain,
% 2.03/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 2.03/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 2.03/1.00      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_3241,c_2691]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3928,plain,
% 2.03/1.00      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.03/1.00      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 2.03/1.00      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.03/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_3595]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3991,plain,
% 2.03/1.00      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 2.03/1.00      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.03/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 2.03/1.00      inference(light_normalisation,[status(thm)],[c_3928,c_3678]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3998,plain,
% 2.03/1.00      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.03/1.00      | r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 2.03/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 2.03/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3991,c_3944]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_4011,plain,
% 2.03/1.00      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.03/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 2.03/1.00      inference(forward_subsumption_resolution,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_4004,c_3944,c_3998]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_5,plain,
% 2.03/1.00      ( v4_pre_topc(k2_struct_0(X0),X0)
% 2.03/1.00      | ~ v2_pre_topc(X0)
% 2.03/1.00      | ~ l1_pre_topc(X0) ),
% 2.03/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_7,plain,
% 2.03/1.00      ( ~ v4_pre_topc(X0,X1)
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/1.00      | ~ l1_pre_topc(X1)
% 2.03/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 2.03/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_414,plain,
% 2.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/1.00      | ~ v2_pre_topc(X2)
% 2.03/1.00      | ~ l1_pre_topc(X2)
% 2.03/1.00      | ~ l1_pre_topc(X1)
% 2.03/1.00      | X1 != X2
% 2.03/1.00      | k2_pre_topc(X1,X0) = X0
% 2.03/1.00      | k2_struct_0(X2) != X0 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_7]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_415,plain,
% 2.03/1.00      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.03/1.00      | ~ v2_pre_topc(X0)
% 2.03/1.00      | ~ l1_pre_topc(X0)
% 2.03/1.00      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_414]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2,plain,
% 2.03/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.03/1.00      | ~ l1_struct_0(X0) ),
% 2.03/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_419,plain,
% 2.03/1.00      ( ~ v2_pre_topc(X0)
% 2.03/1.00      | ~ l1_pre_topc(X0)
% 2.03/1.00      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 2.03/1.00      inference(global_propositional_subsumption,[status(thm)],[c_415,c_3,c_2]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_529,plain,
% 2.03/1.00      ( ~ l1_pre_topc(X0)
% 2.03/1.00      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
% 2.03/1.00      | sK0 != X0 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_419,c_30]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_530,plain,
% 2.03/1.00      ( ~ l1_pre_topc(sK0)
% 2.03/1.00      | k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_529]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_96,plain,
% 2.03/1.00      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ l1_struct_0(sK0) ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_417,plain,
% 2.03/1.00      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | ~ v2_pre_topc(sK0)
% 2.03/1.00      | ~ l1_pre_topc(sK0)
% 2.03/1.00      | k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_415]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_532,plain,
% 2.03/1.00      ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_530,c_30,c_29,c_93,c_96,c_417]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_8,plain,
% 2.03/1.00      ( v1_tops_1(X0,X1)
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/1.00      | ~ l1_pre_topc(X1)
% 2.03/1.00      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 2.03/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_672,plain,
% 2.03/1.00      ( v1_tops_1(X0,X1)
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/1.00      | k2_pre_topc(X1,X0) != k2_struct_0(X1)
% 2.03/1.00      | sK0 != X1 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_673,plain,
% 2.03/1.00      ( v1_tops_1(X0,sK0)
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_672]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_11,plain,
% 2.03/1.00      ( ~ v1_tops_1(X0,X1)
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/1.00      | ~ l1_pre_topc(X1)
% 2.03/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.03/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_627,plain,
% 2.03/1.00      ( ~ v1_tops_1(X0,X1)
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 2.03/1.00      | sK0 != X1 ),
% 2.03/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_628,plain,
% 2.03/1.00      ( ~ v1_tops_1(X0,sK0)
% 2.03/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | k2_pre_topc(sK0,X0) = u1_struct_0(sK0) ),
% 2.03/1.00      inference(unflattening,[status(thm)],[c_627]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_706,plain,
% 2.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.03/1.00      | k2_pre_topc(sK0,X0) = u1_struct_0(sK0)
% 2.03/1.00      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
% 2.03/1.00      inference(resolution,[status(thm)],[c_673,c_628]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3934,plain,
% 2.03/1.00      ( k2_pre_topc(sK0,X0) = u1_struct_0(sK0)
% 2.03/1.00      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0)
% 2.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_4204,plain,
% 2.03/1.00      ( k2_pre_topc(sK0,k2_struct_0(sK0)) = u1_struct_0(sK0)
% 2.03/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_532,c_3934]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_4205,plain,
% 2.03/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0)
% 2.03/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.03/1.00      inference(light_normalisation,[status(thm)],[c_4204,c_532]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_34,plain,
% 2.03/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_92,plain,
% 2.03/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_94,plain,
% 2.03/1.00      ( l1_pre_topc(sK0) != iProver_top | l1_struct_0(sK0) = iProver_top ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_92]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_95,plain,
% 2.03/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.03/1.00      | l1_struct_0(X0) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_97,plain,
% 2.03/1.00      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.03/1.00      | l1_struct_0(sK0) != iProver_top ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_95]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_4208,plain,
% 2.03/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_4205,c_34,c_94,c_97]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_4374,plain,
% 2.03/1.00      ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 2.03/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.03/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.03/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 2.03/1.00      inference(light_normalisation,[status(thm)],[c_4011,c_4208]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_4375,plain,
% 2.03/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 2.03/1.00      inference(equality_resolution_simp,[status(thm)],[c_4374]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3935,plain,
% 2.03/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_4377,plain,
% 2.03/1.00      ( $false ),
% 2.03/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4375,c_3935]) ).
% 2.03/1.00  
% 2.03/1.00  
% 2.03/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.03/1.00  
% 2.03/1.00  ------                               Statistics
% 2.03/1.00  
% 2.03/1.00  ------ General
% 2.03/1.00  
% 2.03/1.00  abstr_ref_over_cycles:                  0
% 2.03/1.00  abstr_ref_under_cycles:                 0
% 2.03/1.00  gc_basic_clause_elim:                   0
% 2.03/1.00  forced_gc_time:                         0
% 2.03/1.00  parsing_time:                           0.011
% 2.03/1.00  unif_index_cands_time:                  0.
% 2.03/1.00  unif_index_add_time:                    0.
% 2.03/1.00  orderings_time:                         0.
% 2.03/1.00  out_proof_time:                         0.015
% 2.03/1.00  total_time:                             0.179
% 2.03/1.00  num_of_symbols:                         59
% 2.03/1.00  num_of_terms:                           1710
% 2.03/1.00  
% 2.03/1.00  ------ Preprocessing
% 2.03/1.00  
% 2.03/1.00  num_of_splits:                          0
% 2.03/1.00  num_of_split_atoms:                     0
% 2.03/1.00  num_of_reused_defs:                     0
% 2.03/1.00  num_eq_ax_congr_red:                    11
% 2.03/1.00  num_of_sem_filtered_clauses:            1
% 2.03/1.00  num_of_subtypes:                        0
% 2.03/1.00  monotx_restored_types:                  0
% 2.03/1.00  sat_num_of_epr_types:                   0
% 2.03/1.00  sat_num_of_non_cyclic_types:            0
% 2.03/1.00  sat_guarded_non_collapsed_types:        0
% 2.03/1.00  num_pure_diseq_elim:                    0
% 2.03/1.00  simp_replaced_by:                       0
% 2.03/1.00  res_preprocessed:                       94
% 2.03/1.00  prep_upred:                             0
% 2.03/1.00  prep_unflattend:                        46
% 2.03/1.00  smt_new_axioms:                         0
% 2.03/1.00  pred_elim_cands:                        2
% 2.03/1.00  pred_elim:                              14
% 2.03/1.00  pred_elim_cl:                           17
% 2.03/1.00  pred_elim_cycles:                       26
% 2.03/1.00  merged_defs:                            2
% 2.03/1.00  merged_defs_ncl:                        0
% 2.03/1.00  bin_hyper_res:                          2
% 2.03/1.00  prep_cycles:                            4
% 2.03/1.00  pred_elim_time:                         0.106
% 2.03/1.00  splitting_time:                         0.
% 2.03/1.00  sem_filter_time:                        0.
% 2.03/1.00  monotx_time:                            0.
% 2.03/1.00  subtype_inf_time:                       0.
% 2.03/1.00  
% 2.03/1.00  ------ Problem properties
% 2.03/1.00  
% 2.03/1.00  clauses:                                13
% 2.03/1.00  conjectures:                            2
% 2.03/1.00  epr:                                    0
% 2.03/1.00  horn:                                   11
% 2.03/1.00  ground:                                 9
% 2.03/1.00  unary:                                  7
% 2.03/1.00  binary:                                 0
% 2.03/1.00  lits:                                   41
% 2.03/1.00  lits_eq:                                19
% 2.03/1.00  fd_pure:                                0
% 2.03/1.00  fd_pseudo:                              0
% 2.03/1.00  fd_cond:                                0
% 2.03/1.00  fd_pseudo_cond:                         0
% 2.03/1.00  ac_symbols:                             0
% 2.03/1.00  
% 2.03/1.00  ------ Propositional Solver
% 2.03/1.00  
% 2.03/1.00  prop_solver_calls:                      24
% 2.03/1.00  prop_fast_solver_calls:                 1744
% 2.03/1.00  smt_solver_calls:                       0
% 2.03/1.00  smt_fast_solver_calls:                  0
% 2.03/1.00  prop_num_of_clauses:                    680
% 2.03/1.00  prop_preprocess_simplified:             2614
% 2.03/1.00  prop_fo_subsumed:                       56
% 2.03/1.00  prop_solver_time:                       0.
% 2.03/1.00  smt_solver_time:                        0.
% 2.03/1.00  smt_fast_solver_time:                   0.
% 2.03/1.00  prop_fast_solver_time:                  0.
% 2.03/1.00  prop_unsat_core_time:                   0.
% 2.03/1.00  
% 2.03/1.00  ------ QBF
% 2.03/1.00  
% 2.03/1.00  qbf_q_res:                              0
% 2.03/1.00  qbf_num_tautologies:                    0
% 2.03/1.00  qbf_prep_cycles:                        0
% 2.03/1.00  
% 2.03/1.00  ------ BMC1
% 2.03/1.00  
% 2.03/1.00  bmc1_current_bound:                     -1
% 2.03/1.00  bmc1_last_solved_bound:                 -1
% 2.03/1.00  bmc1_unsat_core_size:                   -1
% 2.03/1.00  bmc1_unsat_core_parents_size:           -1
% 2.03/1.00  bmc1_merge_next_fun:                    0
% 2.03/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.03/1.00  
% 2.03/1.00  ------ Instantiation
% 2.03/1.00  
% 2.03/1.00  inst_num_of_clauses:                    102
% 2.03/1.00  inst_num_in_passive:                    37
% 2.03/1.00  inst_num_in_active:                     58
% 2.03/1.00  inst_num_in_unprocessed:                7
% 2.03/1.00  inst_num_of_loops:                      60
% 2.03/1.00  inst_num_of_learning_restarts:          0
% 2.03/1.00  inst_num_moves_active_passive:          0
% 2.03/1.00  inst_lit_activity:                      0
% 2.03/1.00  inst_lit_activity_moves:                0
% 2.03/1.00  inst_num_tautologies:                   0
% 2.03/1.00  inst_num_prop_implied:                  0
% 2.03/1.00  inst_num_existing_simplified:           0
% 2.03/1.00  inst_num_eq_res_simplified:             0
% 2.03/1.00  inst_num_child_elim:                    0
% 2.03/1.00  inst_num_of_dismatching_blockings:      14
% 2.03/1.00  inst_num_of_non_proper_insts:           50
% 2.03/1.00  inst_num_of_duplicates:                 0
% 2.03/1.00  inst_inst_num_from_inst_to_res:         0
% 2.03/1.00  inst_dismatching_checking_time:         0.
% 2.03/1.00  
% 2.03/1.00  ------ Resolution
% 2.03/1.00  
% 2.03/1.00  res_num_of_clauses:                     0
% 2.03/1.00  res_num_in_passive:                     0
% 2.03/1.00  res_num_in_active:                      0
% 2.03/1.00  res_num_of_loops:                       98
% 2.03/1.00  res_forward_subset_subsumed:            5
% 2.03/1.00  res_backward_subset_subsumed:           0
% 2.03/1.00  res_forward_subsumed:                   6
% 2.03/1.00  res_backward_subsumed:                  10
% 2.03/1.00  res_forward_subsumption_resolution:     2
% 2.03/1.00  res_backward_subsumption_resolution:    0
% 2.03/1.00  res_clause_to_clause_subsumption:       243
% 2.03/1.00  res_orphan_elimination:                 0
% 2.03/1.00  res_tautology_del:                      17
% 2.03/1.00  res_num_eq_res_simplified:              1
% 2.03/1.00  res_num_sel_changes:                    0
% 2.03/1.00  res_moves_from_active_to_pass:          0
% 2.03/1.00  
% 2.03/1.00  ------ Superposition
% 2.03/1.00  
% 2.03/1.00  sup_time_total:                         0.
% 2.03/1.00  sup_time_generating:                    0.
% 2.03/1.00  sup_time_sim_full:                      0.
% 2.03/1.00  sup_time_sim_immed:                     0.
% 2.03/1.00  
% 2.03/1.00  sup_num_of_clauses:                     10
% 2.03/1.00  sup_num_in_active:                      7
% 2.03/1.00  sup_num_in_passive:                     3
% 2.03/1.00  sup_num_of_loops:                       11
% 2.03/1.00  sup_fw_superposition:                   2
% 2.03/1.00  sup_bw_superposition:                   0
% 2.03/1.00  sup_immediate_simplified:               2
% 2.03/1.00  sup_given_eliminated:                   0
% 2.03/1.00  comparisons_done:                       0
% 2.03/1.00  comparisons_avoided:                    0
% 2.03/1.00  
% 2.03/1.00  ------ Simplifications
% 2.03/1.00  
% 2.03/1.00  
% 2.03/1.00  sim_fw_subset_subsumed:                 1
% 2.03/1.00  sim_bw_subset_subsumed:                 0
% 2.03/1.00  sim_fw_subsumed:                        0
% 2.03/1.00  sim_bw_subsumed:                        2
% 2.03/1.00  sim_fw_subsumption_res:                 5
% 2.03/1.00  sim_bw_subsumption_res:                 0
% 2.03/1.00  sim_tautology_del:                      1
% 2.03/1.00  sim_eq_tautology_del:                   0
% 2.03/1.00  sim_eq_res_simp:                        1
% 2.03/1.00  sim_fw_demodulated:                     0
% 2.03/1.00  sim_bw_demodulated:                     4
% 2.03/1.00  sim_light_normalised:                   7
% 2.03/1.00  sim_joinable_taut:                      0
% 2.03/1.00  sim_joinable_simp:                      0
% 2.03/1.00  sim_ac_normalised:                      0
% 2.03/1.00  sim_smt_subsumption:                    0
% 2.03/1.00  
%------------------------------------------------------------------------------
