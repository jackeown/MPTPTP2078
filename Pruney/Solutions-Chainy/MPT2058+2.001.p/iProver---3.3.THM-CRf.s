%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:14 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  255 (1753 expanded)
%              Number of clauses        :  162 ( 378 expanded)
%              Number of leaves         :   21 ( 488 expanded)
%              Depth                    :   31
%              Number of atoms          : 1516 (16093 expanded)
%              Number of equality atoms :  248 ( 572 expanded)
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

fof(f41,plain,(
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
    inference(flattening,[],[f41])).

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
    inference(nnf_transformation,[],[f42])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_waybel_7(X0,X1,X2)
            | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & ( r1_waybel_7(X0,X1,X2)
            | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_waybel_7(X0,X1,sK3)
          | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3) )
        & ( r1_waybel_7(X0,X1,sK3)
          | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
            ( ( ~ r1_waybel_7(X0,sK2,X2)
              | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2) )
            & ( r1_waybel_7(X0,sK2,X2)
              | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
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
              ( ( ~ r1_waybel_7(sK1,X1,X2)
                | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2) )
              & ( r1_waybel_7(sK1,X1,X2)
                | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ r1_waybel_7(sK1,sK2,sK3)
      | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) )
    & ( r1_waybel_7(sK1,sK2,sK3)
      | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) )
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
    & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))
    & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))
    & ~ v1_xboole_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f52,f51,f50])).

fof(f81,plain,(
    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f96,plain,(
    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f81,f64])).

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

fof(f31,plain,(
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
    inference(flattening,[],[f31])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
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
    inference(definition_unfolding,[],[f68,f64,f64,f64])).

fof(f86,plain,
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f53])).

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

fof(f37,plain,(
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
    inference(flattening,[],[f37])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f76,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f95,plain,(
    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f82,f64])).

fof(f79,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(definition_unfolding,[],[f83,f64])).

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

fof(f39,plain,(
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
    inference(flattening,[],[f39])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f75,f64,f64,f64,f64])).

fof(f80,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f97,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(definition_unfolding,[],[f80,f64])).

fof(f85,plain,
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f47])).

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

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
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
    inference(definition_unfolding,[],[f70,f64,f64,f64])).

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

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
      | ~ v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1)))
      | ~ v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f71,f64,f64,f64,f64])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
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
    inference(definition_unfolding,[],[f69,f64,f64,f64])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
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
    inference(definition_unfolding,[],[f72,f64,f64,f64,f64])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f43])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

cnf(c_26,negated_conjecture,
    ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_12,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_21,negated_conjecture,
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_232,plain,
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_537,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_538,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_542,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_31,c_29])).

cnf(c_1061,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
    | sK3 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_232,c_542])).

cnf(c_1062,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_1061])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1064,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1062,c_23])).

cnf(c_1065,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_1064])).

cnf(c_1101,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_1065])).

cnf(c_1102,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1101])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_90,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1106,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1102,c_31,c_29,c_90])).

cnf(c_25,negated_conjecture,
    ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1952,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1106,c_25])).

cnf(c_1953,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1952])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1957,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1953,c_28])).

cnf(c_1958,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1957])).

cnf(c_2301,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1958])).

cnf(c_2857,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2301])).

cnf(c_3337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_2857])).

cnf(c_3698,plain,
    ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3337])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_612,plain,
    ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_613,plain,
    ( k2_pre_topc(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_7,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_669,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_670,plain,
    ( v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_11,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_624,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_625,plain,
    ( ~ v1_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_704,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,X0) = u1_struct_0(sK1)
    | k2_pre_topc(sK1,X0) != k2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_670,c_625])).

cnf(c_3705,plain,
    ( k2_pre_topc(sK1,X0) = u1_struct_0(sK1)
    | k2_pre_topc(sK1,X0) != k2_struct_0(sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_4242,plain,
    ( k2_pre_topc(sK1,k2_struct_0(sK1)) = u1_struct_0(sK1)
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_3705])).

cnf(c_4243,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4242,c_613])).

cnf(c_34,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_89,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_91,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_3,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_92,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_94,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_4320,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4243,c_34,c_91,c_94])).

cnf(c_4559,plain,
    ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3698,c_4320])).

cnf(c_4569,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4559])).

cnf(c_4738,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4569])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3338,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2857])).

cnf(c_3697,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) != iProver_top
    | r1_waybel_7(sK1,sK2,sK3) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3338])).

cnf(c_20,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_27,negated_conjecture,
    ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_453,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_454,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK2)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_458,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_28])).

cnf(c_459,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(renaming,[status(thm)],[c_458])).

cnf(c_617,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_29])).

cnf(c_618,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_1459,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_459,c_618])).

cnf(c_1460,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v2_struct_0(sK1)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_1459])).

cnf(c_1462,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1460,c_31,c_26,c_25,c_24])).

cnf(c_2866,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1462])).

cnf(c_3810,plain,
    ( r1_waybel_7(sK1,sK2,sK3) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3697,c_2866])).

cnf(c_22,negated_conjecture,
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_234,plain,
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_504,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_505,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_509,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_31,c_29])).

cnf(c_1035,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
    | sK3 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_234,c_509])).

cnf(c_1036,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_1035])).

cnf(c_1038,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | r1_waybel_7(sK1,sK2,sK3)
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1036,c_23])).

cnf(c_1039,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_1038])).

cnf(c_1149,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_1039])).

cnf(c_1150,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1149])).

cnf(c_1154,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1150,c_31,c_29,c_90])).

cnf(c_1907,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1154,c_25])).

cnf(c_1908,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1907])).

cnf(c_1912,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | r1_waybel_7(sK1,sK2,sK3)
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1908,c_28])).

cnf(c_1913,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1912])).

cnf(c_2339,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1913])).

cnf(c_2853,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2339])).

cnf(c_3339,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2853])).

cnf(c_3699,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) = iProver_top
    | r1_waybel_7(sK1,sK2,sK3) = iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3339])).

cnf(c_3787,plain,
    ( r1_waybel_7(sK1,sK2,sK3) = iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3699,c_2866])).

cnf(c_3816,plain,
    ( v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3810,c_3787])).

cnf(c_14,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1510,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_618])).

cnf(c_1511,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1510])).

cnf(c_1515,plain,
    ( v4_orders_2(k3_yellow19(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1511,c_31])).

cnf(c_1516,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1515])).

cnf(c_1847,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1516,c_25])).

cnf(c_1848,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1847])).

cnf(c_1852,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1848,c_28])).

cnf(c_1853,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1852])).

cnf(c_2400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1853])).

cnf(c_2845,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2400])).

cnf(c_3879,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(k2_struct_0(sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2845])).

cnf(c_3880,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3879])).

cnf(c_17,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_15,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_177,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_15])).

cnf(c_178,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_177])).

cnf(c_1477,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_178,c_618])).

cnf(c_1478,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1477])).

cnf(c_1482,plain,
    ( ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1478,c_31])).

cnf(c_1483,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1482])).

cnf(c_1877,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1483,c_25])).

cnf(c_1878,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1877])).

cnf(c_1882,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1878,c_28])).

cnf(c_1883,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1882])).

cnf(c_2377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1883])).

cnf(c_2849,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2377])).

cnf(c_3885,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | ~ v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(k2_struct_0(sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2849])).

cnf(c_3886,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3885])).

cnf(c_16,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_414,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_415,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_419,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_28])).

cnf(c_420,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_419])).

cnf(c_1550,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_420,c_618])).

cnf(c_1551,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1550])).

cnf(c_1555,plain,
    ( v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1551,c_31])).

cnf(c_1556,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1555])).

cnf(c_1997,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_1556])).

cnf(c_2275,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_1997])).

cnf(c_2861,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2275])).

cnf(c_3891,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(k2_struct_0(sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_2861])).

cnf(c_3892,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3891])).

cnf(c_3341,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4101,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) = k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3341])).

cnf(c_6,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_570,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_30])).

cnf(c_571,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_84,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_573,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_31,c_30,c_29,c_84])).

cnf(c_3707,plain,
    ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3712,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4111,plain,
    ( v1_xboole_0(sK0(sK1)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3707,c_3712])).

cnf(c_32,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_33,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_86,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_88,plain,
    ( v2_struct_0(sK1) = iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(sK0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_4144,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4111,c_32,c_33,c_34,c_88])).

cnf(c_4325,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4320,c_4144])).

cnf(c_4666,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_3341])).

cnf(c_4740,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4738,c_34,c_39,c_91,c_94,c_3816,c_3880,c_3886,c_3892,c_4101,c_4325,c_4569,c_4666])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3713,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3726,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3713,c_0])).

cnf(c_4745,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4740,c_3726])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.53/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/0.99  
% 2.53/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/0.99  
% 2.53/0.99  ------  iProver source info
% 2.53/0.99  
% 2.53/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.53/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/0.99  git: non_committed_changes: false
% 2.53/0.99  git: last_make_outside_of_git: false
% 2.53/0.99  
% 2.53/0.99  ------ 
% 2.53/0.99  
% 2.53/0.99  ------ Input Options
% 2.53/0.99  
% 2.53/0.99  --out_options                           all
% 2.53/0.99  --tptp_safe_out                         true
% 2.53/0.99  --problem_path                          ""
% 2.53/0.99  --include_path                          ""
% 2.53/0.99  --clausifier                            res/vclausify_rel
% 2.53/0.99  --clausifier_options                    --mode clausify
% 2.53/0.99  --stdin                                 false
% 2.53/0.99  --stats_out                             all
% 2.53/0.99  
% 2.53/0.99  ------ General Options
% 2.53/0.99  
% 2.53/0.99  --fof                                   false
% 2.53/0.99  --time_out_real                         305.
% 2.53/0.99  --time_out_virtual                      -1.
% 2.53/0.99  --symbol_type_check                     false
% 2.53/0.99  --clausify_out                          false
% 2.53/0.99  --sig_cnt_out                           false
% 2.53/0.99  --trig_cnt_out                          false
% 2.53/0.99  --trig_cnt_out_tolerance                1.
% 2.53/0.99  --trig_cnt_out_sk_spl                   false
% 2.53/0.99  --abstr_cl_out                          false
% 2.53/0.99  
% 2.53/0.99  ------ Global Options
% 2.53/0.99  
% 2.53/0.99  --schedule                              default
% 2.53/0.99  --add_important_lit                     false
% 2.53/0.99  --prop_solver_per_cl                    1000
% 2.53/0.99  --min_unsat_core                        false
% 2.53/0.99  --soft_assumptions                      false
% 2.53/0.99  --soft_lemma_size                       3
% 2.53/0.99  --prop_impl_unit_size                   0
% 2.53/0.99  --prop_impl_unit                        []
% 2.53/0.99  --share_sel_clauses                     true
% 2.53/0.99  --reset_solvers                         false
% 2.53/0.99  --bc_imp_inh                            [conj_cone]
% 2.53/0.99  --conj_cone_tolerance                   3.
% 2.53/0.99  --extra_neg_conj                        none
% 2.53/0.99  --large_theory_mode                     true
% 2.53/0.99  --prolific_symb_bound                   200
% 2.53/0.99  --lt_threshold                          2000
% 2.53/0.99  --clause_weak_htbl                      true
% 2.53/0.99  --gc_record_bc_elim                     false
% 2.53/0.99  
% 2.53/0.99  ------ Preprocessing Options
% 2.53/0.99  
% 2.53/0.99  --preprocessing_flag                    true
% 2.53/0.99  --time_out_prep_mult                    0.1
% 2.53/0.99  --splitting_mode                        input
% 2.53/0.99  --splitting_grd                         true
% 2.53/0.99  --splitting_cvd                         false
% 2.53/0.99  --splitting_cvd_svl                     false
% 2.53/0.99  --splitting_nvd                         32
% 2.53/0.99  --sub_typing                            true
% 2.53/0.99  --prep_gs_sim                           true
% 2.53/0.99  --prep_unflatten                        true
% 2.53/0.99  --prep_res_sim                          true
% 2.53/0.99  --prep_upred                            true
% 2.53/0.99  --prep_sem_filter                       exhaustive
% 2.53/0.99  --prep_sem_filter_out                   false
% 2.53/0.99  --pred_elim                             true
% 2.53/0.99  --res_sim_input                         true
% 2.53/0.99  --eq_ax_congr_red                       true
% 2.53/0.99  --pure_diseq_elim                       true
% 2.53/0.99  --brand_transform                       false
% 2.53/0.99  --non_eq_to_eq                          false
% 2.53/0.99  --prep_def_merge                        true
% 2.53/0.99  --prep_def_merge_prop_impl              false
% 2.53/0.99  --prep_def_merge_mbd                    true
% 2.53/0.99  --prep_def_merge_tr_red                 false
% 2.53/0.99  --prep_def_merge_tr_cl                  false
% 2.53/0.99  --smt_preprocessing                     true
% 2.53/0.99  --smt_ac_axioms                         fast
% 2.53/0.99  --preprocessed_out                      false
% 2.53/0.99  --preprocessed_stats                    false
% 2.53/0.99  
% 2.53/0.99  ------ Abstraction refinement Options
% 2.53/0.99  
% 2.53/0.99  --abstr_ref                             []
% 2.53/0.99  --abstr_ref_prep                        false
% 2.53/0.99  --abstr_ref_until_sat                   false
% 2.53/0.99  --abstr_ref_sig_restrict                funpre
% 2.53/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/0.99  --abstr_ref_under                       []
% 2.53/0.99  
% 2.53/0.99  ------ SAT Options
% 2.53/0.99  
% 2.53/0.99  --sat_mode                              false
% 2.53/0.99  --sat_fm_restart_options                ""
% 2.53/0.99  --sat_gr_def                            false
% 2.53/0.99  --sat_epr_types                         true
% 2.53/0.99  --sat_non_cyclic_types                  false
% 2.53/0.99  --sat_finite_models                     false
% 2.53/0.99  --sat_fm_lemmas                         false
% 2.53/0.99  --sat_fm_prep                           false
% 2.53/0.99  --sat_fm_uc_incr                        true
% 2.53/0.99  --sat_out_model                         small
% 2.53/0.99  --sat_out_clauses                       false
% 2.53/0.99  
% 2.53/0.99  ------ QBF Options
% 2.53/0.99  
% 2.53/0.99  --qbf_mode                              false
% 2.53/0.99  --qbf_elim_univ                         false
% 2.53/0.99  --qbf_dom_inst                          none
% 2.53/0.99  --qbf_dom_pre_inst                      false
% 2.53/0.99  --qbf_sk_in                             false
% 2.53/0.99  --qbf_pred_elim                         true
% 2.53/0.99  --qbf_split                             512
% 2.53/0.99  
% 2.53/0.99  ------ BMC1 Options
% 2.53/0.99  
% 2.53/0.99  --bmc1_incremental                      false
% 2.53/0.99  --bmc1_axioms                           reachable_all
% 2.53/0.99  --bmc1_min_bound                        0
% 2.53/0.99  --bmc1_max_bound                        -1
% 2.53/0.99  --bmc1_max_bound_default                -1
% 2.53/0.99  --bmc1_symbol_reachability              true
% 2.53/0.99  --bmc1_property_lemmas                  false
% 2.53/0.99  --bmc1_k_induction                      false
% 2.53/0.99  --bmc1_non_equiv_states                 false
% 2.53/0.99  --bmc1_deadlock                         false
% 2.53/0.99  --bmc1_ucm                              false
% 2.53/0.99  --bmc1_add_unsat_core                   none
% 2.53/0.99  --bmc1_unsat_core_children              false
% 2.53/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/0.99  --bmc1_out_stat                         full
% 2.53/0.99  --bmc1_ground_init                      false
% 2.53/0.99  --bmc1_pre_inst_next_state              false
% 2.53/0.99  --bmc1_pre_inst_state                   false
% 2.53/0.99  --bmc1_pre_inst_reach_state             false
% 2.53/0.99  --bmc1_out_unsat_core                   false
% 2.53/0.99  --bmc1_aig_witness_out                  false
% 2.53/0.99  --bmc1_verbose                          false
% 2.53/0.99  --bmc1_dump_clauses_tptp                false
% 2.53/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.53/0.99  --bmc1_dump_file                        -
% 2.53/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.53/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.53/0.99  --bmc1_ucm_extend_mode                  1
% 2.53/0.99  --bmc1_ucm_init_mode                    2
% 2.53/0.99  --bmc1_ucm_cone_mode                    none
% 2.53/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.53/0.99  --bmc1_ucm_relax_model                  4
% 2.53/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.53/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/0.99  --bmc1_ucm_layered_model                none
% 2.53/0.99  --bmc1_ucm_max_lemma_size               10
% 2.53/0.99  
% 2.53/0.99  ------ AIG Options
% 2.53/0.99  
% 2.53/0.99  --aig_mode                              false
% 2.53/0.99  
% 2.53/0.99  ------ Instantiation Options
% 2.53/0.99  
% 2.53/0.99  --instantiation_flag                    true
% 2.53/0.99  --inst_sos_flag                         false
% 2.53/0.99  --inst_sos_phase                        true
% 2.53/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/0.99  --inst_lit_sel_side                     num_symb
% 2.53/0.99  --inst_solver_per_active                1400
% 2.53/0.99  --inst_solver_calls_frac                1.
% 2.53/0.99  --inst_passive_queue_type               priority_queues
% 2.53/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/0.99  --inst_passive_queues_freq              [25;2]
% 2.53/0.99  --inst_dismatching                      true
% 2.53/0.99  --inst_eager_unprocessed_to_passive     true
% 2.53/0.99  --inst_prop_sim_given                   true
% 2.53/0.99  --inst_prop_sim_new                     false
% 2.53/0.99  --inst_subs_new                         false
% 2.53/0.99  --inst_eq_res_simp                      false
% 2.53/0.99  --inst_subs_given                       false
% 2.53/0.99  --inst_orphan_elimination               true
% 2.53/0.99  --inst_learning_loop_flag               true
% 2.53/0.99  --inst_learning_start                   3000
% 2.53/0.99  --inst_learning_factor                  2
% 2.53/0.99  --inst_start_prop_sim_after_learn       3
% 2.53/0.99  --inst_sel_renew                        solver
% 2.53/0.99  --inst_lit_activity_flag                true
% 2.53/0.99  --inst_restr_to_given                   false
% 2.53/0.99  --inst_activity_threshold               500
% 2.53/0.99  --inst_out_proof                        true
% 2.53/0.99  
% 2.53/0.99  ------ Resolution Options
% 2.53/0.99  
% 2.53/0.99  --resolution_flag                       true
% 2.53/0.99  --res_lit_sel                           adaptive
% 2.53/0.99  --res_lit_sel_side                      none
% 2.53/0.99  --res_ordering                          kbo
% 2.53/0.99  --res_to_prop_solver                    active
% 2.53/0.99  --res_prop_simpl_new                    false
% 2.53/0.99  --res_prop_simpl_given                  true
% 2.53/0.99  --res_passive_queue_type                priority_queues
% 2.53/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.00  --res_passive_queues_freq               [15;5]
% 2.53/1.00  --res_forward_subs                      full
% 2.53/1.00  --res_backward_subs                     full
% 2.53/1.00  --res_forward_subs_resolution           true
% 2.53/1.00  --res_backward_subs_resolution          true
% 2.53/1.00  --res_orphan_elimination                true
% 2.53/1.00  --res_time_limit                        2.
% 2.53/1.00  --res_out_proof                         true
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Options
% 2.53/1.00  
% 2.53/1.00  --superposition_flag                    true
% 2.53/1.00  --sup_passive_queue_type                priority_queues
% 2.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.00  --demod_completeness_check              fast
% 2.53/1.00  --demod_use_ground                      true
% 2.53/1.00  --sup_to_prop_solver                    passive
% 2.53/1.00  --sup_prop_simpl_new                    true
% 2.53/1.00  --sup_prop_simpl_given                  true
% 2.53/1.00  --sup_fun_splitting                     false
% 2.53/1.00  --sup_smt_interval                      50000
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Simplification Setup
% 2.53/1.00  
% 2.53/1.00  --sup_indices_passive                   []
% 2.53/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_full_bw                           [BwDemod]
% 2.53/1.00  --sup_immed_triv                        [TrivRules]
% 2.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_immed_bw_main                     []
% 2.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  
% 2.53/1.00  ------ Combination Options
% 2.53/1.00  
% 2.53/1.00  --comb_res_mult                         3
% 2.53/1.00  --comb_sup_mult                         2
% 2.53/1.00  --comb_inst_mult                        10
% 2.53/1.00  
% 2.53/1.00  ------ Debug Options
% 2.53/1.00  
% 2.53/1.00  --dbg_backtrace                         false
% 2.53/1.00  --dbg_dump_prop_clauses                 false
% 2.53/1.00  --dbg_dump_prop_clauses_file            -
% 2.53/1.00  --dbg_out_stat                          false
% 2.53/1.00  ------ Parsing...
% 2.53/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/1.00  ------ Proving...
% 2.53/1.00  ------ Problem Properties 
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  clauses                                 21
% 2.53/1.00  conjectures                             4
% 2.53/1.00  EPR                                     2
% 2.53/1.00  Horn                                    17
% 2.53/1.00  unary                                   11
% 2.53/1.00  binary                                  0
% 2.53/1.00  lits                                    60
% 2.53/1.00  lits eq                                 15
% 2.53/1.00  fd_pure                                 0
% 2.53/1.00  fd_pseudo                               0
% 2.53/1.00  fd_cond                                 0
% 2.53/1.00  fd_pseudo_cond                          0
% 2.53/1.00  AC symbols                              0
% 2.53/1.00  
% 2.53/1.00  ------ Schedule dynamic 5 is on 
% 2.53/1.00  
% 2.53/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  ------ 
% 2.53/1.00  Current options:
% 2.53/1.00  ------ 
% 2.53/1.00  
% 2.53/1.00  ------ Input Options
% 2.53/1.00  
% 2.53/1.00  --out_options                           all
% 2.53/1.00  --tptp_safe_out                         true
% 2.53/1.00  --problem_path                          ""
% 2.53/1.00  --include_path                          ""
% 2.53/1.00  --clausifier                            res/vclausify_rel
% 2.53/1.00  --clausifier_options                    --mode clausify
% 2.53/1.00  --stdin                                 false
% 2.53/1.00  --stats_out                             all
% 2.53/1.00  
% 2.53/1.00  ------ General Options
% 2.53/1.00  
% 2.53/1.00  --fof                                   false
% 2.53/1.00  --time_out_real                         305.
% 2.53/1.00  --time_out_virtual                      -1.
% 2.53/1.00  --symbol_type_check                     false
% 2.53/1.00  --clausify_out                          false
% 2.53/1.00  --sig_cnt_out                           false
% 2.53/1.00  --trig_cnt_out                          false
% 2.53/1.00  --trig_cnt_out_tolerance                1.
% 2.53/1.00  --trig_cnt_out_sk_spl                   false
% 2.53/1.00  --abstr_cl_out                          false
% 2.53/1.00  
% 2.53/1.00  ------ Global Options
% 2.53/1.00  
% 2.53/1.00  --schedule                              default
% 2.53/1.00  --add_important_lit                     false
% 2.53/1.00  --prop_solver_per_cl                    1000
% 2.53/1.00  --min_unsat_core                        false
% 2.53/1.00  --soft_assumptions                      false
% 2.53/1.00  --soft_lemma_size                       3
% 2.53/1.00  --prop_impl_unit_size                   0
% 2.53/1.00  --prop_impl_unit                        []
% 2.53/1.00  --share_sel_clauses                     true
% 2.53/1.00  --reset_solvers                         false
% 2.53/1.00  --bc_imp_inh                            [conj_cone]
% 2.53/1.00  --conj_cone_tolerance                   3.
% 2.53/1.00  --extra_neg_conj                        none
% 2.53/1.00  --large_theory_mode                     true
% 2.53/1.00  --prolific_symb_bound                   200
% 2.53/1.00  --lt_threshold                          2000
% 2.53/1.00  --clause_weak_htbl                      true
% 2.53/1.00  --gc_record_bc_elim                     false
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing Options
% 2.53/1.00  
% 2.53/1.00  --preprocessing_flag                    true
% 2.53/1.00  --time_out_prep_mult                    0.1
% 2.53/1.00  --splitting_mode                        input
% 2.53/1.00  --splitting_grd                         true
% 2.53/1.00  --splitting_cvd                         false
% 2.53/1.00  --splitting_cvd_svl                     false
% 2.53/1.00  --splitting_nvd                         32
% 2.53/1.00  --sub_typing                            true
% 2.53/1.00  --prep_gs_sim                           true
% 2.53/1.00  --prep_unflatten                        true
% 2.53/1.00  --prep_res_sim                          true
% 2.53/1.00  --prep_upred                            true
% 2.53/1.00  --prep_sem_filter                       exhaustive
% 2.53/1.00  --prep_sem_filter_out                   false
% 2.53/1.00  --pred_elim                             true
% 2.53/1.00  --res_sim_input                         true
% 2.53/1.00  --eq_ax_congr_red                       true
% 2.53/1.00  --pure_diseq_elim                       true
% 2.53/1.00  --brand_transform                       false
% 2.53/1.00  --non_eq_to_eq                          false
% 2.53/1.00  --prep_def_merge                        true
% 2.53/1.00  --prep_def_merge_prop_impl              false
% 2.53/1.00  --prep_def_merge_mbd                    true
% 2.53/1.00  --prep_def_merge_tr_red                 false
% 2.53/1.00  --prep_def_merge_tr_cl                  false
% 2.53/1.00  --smt_preprocessing                     true
% 2.53/1.00  --smt_ac_axioms                         fast
% 2.53/1.00  --preprocessed_out                      false
% 2.53/1.00  --preprocessed_stats                    false
% 2.53/1.00  
% 2.53/1.00  ------ Abstraction refinement Options
% 2.53/1.00  
% 2.53/1.00  --abstr_ref                             []
% 2.53/1.00  --abstr_ref_prep                        false
% 2.53/1.00  --abstr_ref_until_sat                   false
% 2.53/1.00  --abstr_ref_sig_restrict                funpre
% 2.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.00  --abstr_ref_under                       []
% 2.53/1.00  
% 2.53/1.00  ------ SAT Options
% 2.53/1.00  
% 2.53/1.00  --sat_mode                              false
% 2.53/1.00  --sat_fm_restart_options                ""
% 2.53/1.00  --sat_gr_def                            false
% 2.53/1.00  --sat_epr_types                         true
% 2.53/1.00  --sat_non_cyclic_types                  false
% 2.53/1.00  --sat_finite_models                     false
% 2.53/1.00  --sat_fm_lemmas                         false
% 2.53/1.00  --sat_fm_prep                           false
% 2.53/1.00  --sat_fm_uc_incr                        true
% 2.53/1.00  --sat_out_model                         small
% 2.53/1.00  --sat_out_clauses                       false
% 2.53/1.00  
% 2.53/1.00  ------ QBF Options
% 2.53/1.00  
% 2.53/1.00  --qbf_mode                              false
% 2.53/1.00  --qbf_elim_univ                         false
% 2.53/1.00  --qbf_dom_inst                          none
% 2.53/1.00  --qbf_dom_pre_inst                      false
% 2.53/1.00  --qbf_sk_in                             false
% 2.53/1.00  --qbf_pred_elim                         true
% 2.53/1.00  --qbf_split                             512
% 2.53/1.00  
% 2.53/1.00  ------ BMC1 Options
% 2.53/1.00  
% 2.53/1.00  --bmc1_incremental                      false
% 2.53/1.00  --bmc1_axioms                           reachable_all
% 2.53/1.00  --bmc1_min_bound                        0
% 2.53/1.00  --bmc1_max_bound                        -1
% 2.53/1.00  --bmc1_max_bound_default                -1
% 2.53/1.00  --bmc1_symbol_reachability              true
% 2.53/1.00  --bmc1_property_lemmas                  false
% 2.53/1.00  --bmc1_k_induction                      false
% 2.53/1.00  --bmc1_non_equiv_states                 false
% 2.53/1.00  --bmc1_deadlock                         false
% 2.53/1.00  --bmc1_ucm                              false
% 2.53/1.00  --bmc1_add_unsat_core                   none
% 2.53/1.00  --bmc1_unsat_core_children              false
% 2.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.00  --bmc1_out_stat                         full
% 2.53/1.00  --bmc1_ground_init                      false
% 2.53/1.00  --bmc1_pre_inst_next_state              false
% 2.53/1.00  --bmc1_pre_inst_state                   false
% 2.53/1.00  --bmc1_pre_inst_reach_state             false
% 2.53/1.00  --bmc1_out_unsat_core                   false
% 2.53/1.00  --bmc1_aig_witness_out                  false
% 2.53/1.00  --bmc1_verbose                          false
% 2.53/1.00  --bmc1_dump_clauses_tptp                false
% 2.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.00  --bmc1_dump_file                        -
% 2.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.00  --bmc1_ucm_extend_mode                  1
% 2.53/1.00  --bmc1_ucm_init_mode                    2
% 2.53/1.00  --bmc1_ucm_cone_mode                    none
% 2.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.00  --bmc1_ucm_relax_model                  4
% 2.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.00  --bmc1_ucm_layered_model                none
% 2.53/1.00  --bmc1_ucm_max_lemma_size               10
% 2.53/1.00  
% 2.53/1.00  ------ AIG Options
% 2.53/1.00  
% 2.53/1.00  --aig_mode                              false
% 2.53/1.00  
% 2.53/1.00  ------ Instantiation Options
% 2.53/1.00  
% 2.53/1.00  --instantiation_flag                    true
% 2.53/1.00  --inst_sos_flag                         false
% 2.53/1.00  --inst_sos_phase                        true
% 2.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.00  --inst_lit_sel_side                     none
% 2.53/1.00  --inst_solver_per_active                1400
% 2.53/1.00  --inst_solver_calls_frac                1.
% 2.53/1.00  --inst_passive_queue_type               priority_queues
% 2.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.00  --inst_passive_queues_freq              [25;2]
% 2.53/1.00  --inst_dismatching                      true
% 2.53/1.00  --inst_eager_unprocessed_to_passive     true
% 2.53/1.00  --inst_prop_sim_given                   true
% 2.53/1.00  --inst_prop_sim_new                     false
% 2.53/1.00  --inst_subs_new                         false
% 2.53/1.00  --inst_eq_res_simp                      false
% 2.53/1.00  --inst_subs_given                       false
% 2.53/1.00  --inst_orphan_elimination               true
% 2.53/1.00  --inst_learning_loop_flag               true
% 2.53/1.00  --inst_learning_start                   3000
% 2.53/1.00  --inst_learning_factor                  2
% 2.53/1.00  --inst_start_prop_sim_after_learn       3
% 2.53/1.00  --inst_sel_renew                        solver
% 2.53/1.00  --inst_lit_activity_flag                true
% 2.53/1.00  --inst_restr_to_given                   false
% 2.53/1.00  --inst_activity_threshold               500
% 2.53/1.00  --inst_out_proof                        true
% 2.53/1.00  
% 2.53/1.00  ------ Resolution Options
% 2.53/1.00  
% 2.53/1.00  --resolution_flag                       false
% 2.53/1.00  --res_lit_sel                           adaptive
% 2.53/1.00  --res_lit_sel_side                      none
% 2.53/1.00  --res_ordering                          kbo
% 2.53/1.00  --res_to_prop_solver                    active
% 2.53/1.00  --res_prop_simpl_new                    false
% 2.53/1.00  --res_prop_simpl_given                  true
% 2.53/1.00  --res_passive_queue_type                priority_queues
% 2.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.00  --res_passive_queues_freq               [15;5]
% 2.53/1.00  --res_forward_subs                      full
% 2.53/1.00  --res_backward_subs                     full
% 2.53/1.00  --res_forward_subs_resolution           true
% 2.53/1.00  --res_backward_subs_resolution          true
% 2.53/1.00  --res_orphan_elimination                true
% 2.53/1.00  --res_time_limit                        2.
% 2.53/1.00  --res_out_proof                         true
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Options
% 2.53/1.00  
% 2.53/1.00  --superposition_flag                    true
% 2.53/1.00  --sup_passive_queue_type                priority_queues
% 2.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.00  --demod_completeness_check              fast
% 2.53/1.00  --demod_use_ground                      true
% 2.53/1.00  --sup_to_prop_solver                    passive
% 2.53/1.00  --sup_prop_simpl_new                    true
% 2.53/1.00  --sup_prop_simpl_given                  true
% 2.53/1.00  --sup_fun_splitting                     false
% 2.53/1.00  --sup_smt_interval                      50000
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Simplification Setup
% 2.53/1.00  
% 2.53/1.00  --sup_indices_passive                   []
% 2.53/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_full_bw                           [BwDemod]
% 2.53/1.00  --sup_immed_triv                        [TrivRules]
% 2.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_immed_bw_main                     []
% 2.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  
% 2.53/1.00  ------ Combination Options
% 2.53/1.00  
% 2.53/1.00  --comb_res_mult                         3
% 2.53/1.00  --comb_sup_mult                         2
% 2.53/1.00  --comb_inst_mult                        10
% 2.53/1.00  
% 2.53/1.00  ------ Debug Options
% 2.53/1.00  
% 2.53/1.00  --dbg_backtrace                         false
% 2.53/1.00  --dbg_dump_prop_clauses                 false
% 2.53/1.00  --dbg_dump_prop_clauses_file            -
% 2.53/1.00  --dbg_out_stat                          false
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  ------ Proving...
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  % SZS status Theorem for theBenchmark.p
% 2.53/1.00  
% 2.53/1.00   Resolution empty clause
% 2.53/1.00  
% 2.53/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/1.00  
% 2.53/1.00  fof(f16,conjecture,(
% 2.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f17,negated_conjecture,(
% 2.53/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.53/1.00    inference(negated_conjecture,[],[f16])).
% 2.53/1.00  
% 2.53/1.00  fof(f41,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f17])).
% 2.53/1.00  
% 2.53/1.00  fof(f42,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f41])).
% 2.53/1.00  
% 2.53/1.00  fof(f48,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/1.00    inference(nnf_transformation,[],[f42])).
% 2.53/1.00  
% 2.53/1.00  fof(f49,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f48])).
% 2.53/1.00  
% 2.53/1.00  fof(f52,plain,(
% 2.53/1.00    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK3) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3)) & (r1_waybel_7(X0,X1,sK3) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f51,plain,(
% 2.53/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK2,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2)) & (r1_waybel_7(X0,sK2,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK2))) )),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f50,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK1,X1,X2) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2)) & (r1_waybel_7(sK1,X1,X2) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f53,plain,(
% 2.53/1.00    (((~r1_waybel_7(sK1,sK2,sK3) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)) & (r1_waybel_7(sK1,sK2,sK3) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f49,f52,f51,f50])).
% 2.53/1.00  
% 2.53/1.00  fof(f81,plain,(
% 2.53/1.00    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 2.53/1.00    inference(cnf_transformation,[],[f53])).
% 2.53/1.00  
% 2.53/1.00  fof(f9,axiom,(
% 2.53/1.00    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f64,plain,(
% 2.53/1.00    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.53/1.00    inference(cnf_transformation,[],[f9])).
% 2.53/1.00  
% 2.53/1.00  fof(f96,plain,(
% 2.53/1.00    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 2.53/1.00    inference(definition_unfolding,[],[f81,f64])).
% 2.53/1.00  
% 2.53/1.00  fof(f11,axiom,(
% 2.53/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f20,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.53/1.00    inference(pure_predicate_removal,[],[f11])).
% 2.53/1.00  
% 2.53/1.00  fof(f31,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f20])).
% 2.53/1.00  
% 2.53/1.00  fof(f32,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f31])).
% 2.53/1.00  
% 2.53/1.00  fof(f68,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f32])).
% 2.53/1.00  
% 2.53/1.00  fof(f87,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f68,f64,f64,f64])).
% 2.53/1.00  
% 2.53/1.00  fof(f86,plain,(
% 2.53/1.00    ~r1_waybel_7(sK1,sK2,sK3) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)),
% 2.53/1.00    inference(cnf_transformation,[],[f53])).
% 2.53/1.00  
% 2.53/1.00  fof(f14,axiom,(
% 2.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f37,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f14])).
% 2.53/1.00  
% 2.53/1.00  fof(f38,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f37])).
% 2.53/1.00  
% 2.53/1.00  fof(f47,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(nnf_transformation,[],[f38])).
% 2.53/1.00  
% 2.53/1.00  fof(f74,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f47])).
% 2.53/1.00  
% 2.53/1.00  fof(f77,plain,(
% 2.53/1.00    v2_pre_topc(sK1)),
% 2.53/1.00    inference(cnf_transformation,[],[f53])).
% 2.53/1.00  
% 2.53/1.00  fof(f76,plain,(
% 2.53/1.00    ~v2_struct_0(sK1)),
% 2.53/1.00    inference(cnf_transformation,[],[f53])).
% 2.53/1.00  
% 2.53/1.00  fof(f78,plain,(
% 2.53/1.00    l1_pre_topc(sK1)),
% 2.53/1.00    inference(cnf_transformation,[],[f53])).
% 2.53/1.00  
% 2.53/1.00  fof(f84,plain,(
% 2.53/1.00    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.53/1.00    inference(cnf_transformation,[],[f53])).
% 2.53/1.00  
% 2.53/1.00  fof(f5,axiom,(
% 2.53/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f25,plain,(
% 2.53/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f5])).
% 2.53/1.00  
% 2.53/1.00  fof(f58,plain,(
% 2.53/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f25])).
% 2.53/1.00  
% 2.53/1.00  fof(f82,plain,(
% 2.53/1.00    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 2.53/1.00    inference(cnf_transformation,[],[f53])).
% 2.53/1.00  
% 2.53/1.00  fof(f95,plain,(
% 2.53/1.00    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 2.53/1.00    inference(definition_unfolding,[],[f82,f64])).
% 2.53/1.00  
% 2.53/1.00  fof(f79,plain,(
% 2.53/1.00    ~v1_xboole_0(sK2)),
% 2.53/1.00    inference(cnf_transformation,[],[f53])).
% 2.53/1.00  
% 2.53/1.00  fof(f8,axiom,(
% 2.53/1.00    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f29,plain,(
% 2.53/1.00    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f8])).
% 2.53/1.00  
% 2.53/1.00  fof(f63,plain,(
% 2.53/1.00    ( ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f29])).
% 2.53/1.00  
% 2.53/1.00  fof(f7,axiom,(
% 2.53/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f28,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f7])).
% 2.53/1.00  
% 2.53/1.00  fof(f45,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.53/1.00    inference(nnf_transformation,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f62,plain,(
% 2.53/1.00    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f45])).
% 2.53/1.00  
% 2.53/1.00  fof(f10,axiom,(
% 2.53/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f30,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f10])).
% 2.53/1.00  
% 2.53/1.00  fof(f46,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.53/1.00    inference(nnf_transformation,[],[f30])).
% 2.53/1.00  
% 2.53/1.00  fof(f65,plain,(
% 2.53/1.00    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f46])).
% 2.53/1.00  
% 2.53/1.00  fof(f4,axiom,(
% 2.53/1.00    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f24,plain,(
% 2.53/1.00    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f4])).
% 2.53/1.00  
% 2.53/1.00  fof(f57,plain,(
% 2.53/1.00    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f24])).
% 2.53/1.00  
% 2.53/1.00  fof(f83,plain,(
% 2.53/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))),
% 2.53/1.00    inference(cnf_transformation,[],[f53])).
% 2.53/1.00  
% 2.53/1.00  fof(f94,plain,(
% 2.53/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))),
% 2.53/1.00    inference(definition_unfolding,[],[f83,f64])).
% 2.53/1.00  
% 2.53/1.00  fof(f15,axiom,(
% 2.53/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f39,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f15])).
% 2.53/1.00  
% 2.53/1.00  fof(f40,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f39])).
% 2.53/1.00  
% 2.53/1.00  fof(f75,plain,(
% 2.53/1.00    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f40])).
% 2.53/1.00  
% 2.53/1.00  fof(f93,plain,(
% 2.53/1.00    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f75,f64,f64,f64,f64])).
% 2.53/1.00  
% 2.53/1.00  fof(f80,plain,(
% 2.53/1.00    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))),
% 2.53/1.00    inference(cnf_transformation,[],[f53])).
% 2.53/1.00  
% 2.53/1.00  fof(f97,plain,(
% 2.53/1.00    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))),
% 2.53/1.00    inference(definition_unfolding,[],[f80,f64])).
% 2.53/1.00  
% 2.53/1.00  fof(f85,plain,(
% 2.53/1.00    r1_waybel_7(sK1,sK2,sK3) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)),
% 2.53/1.00    inference(cnf_transformation,[],[f53])).
% 2.53/1.00  
% 2.53/1.00  fof(f73,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f47])).
% 2.53/1.00  
% 2.53/1.00  fof(f12,axiom,(
% 2.53/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f18,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.53/1.00    inference(pure_predicate_removal,[],[f12])).
% 2.53/1.00  
% 2.53/1.00  fof(f21,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.53/1.00    inference(pure_predicate_removal,[],[f18])).
% 2.53/1.00  
% 2.53/1.00  fof(f33,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f21])).
% 2.53/1.00  
% 2.53/1.00  fof(f34,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f33])).
% 2.53/1.00  
% 2.53/1.00  fof(f70,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f34])).
% 2.53/1.00  
% 2.53/1.00  fof(f89,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f70,f64,f64,f64])).
% 2.53/1.00  
% 2.53/1.00  fof(f13,axiom,(
% 2.53/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f19,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.53/1.00    inference(pure_predicate_removal,[],[f13])).
% 2.53/1.00  
% 2.53/1.00  fof(f35,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f19])).
% 2.53/1.00  
% 2.53/1.00  fof(f36,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f35])).
% 2.53/1.00  
% 2.53/1.00  fof(f71,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f36])).
% 2.53/1.00  
% 2.53/1.00  fof(f92,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f71,f64,f64,f64,f64])).
% 2.53/1.00  
% 2.53/1.00  fof(f69,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f34])).
% 2.53/1.00  
% 2.53/1.00  fof(f90,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f69,f64,f64,f64])).
% 2.53/1.00  
% 2.53/1.00  fof(f72,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f36])).
% 2.53/1.00  
% 2.53/1.00  fof(f91,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f72,f64,f64,f64,f64])).
% 2.53/1.00  
% 2.53/1.00  fof(f6,axiom,(
% 2.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f22,plain,(
% 2.53/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.53/1.00    inference(pure_predicate_removal,[],[f6])).
% 2.53/1.00  
% 2.53/1.00  fof(f26,plain,(
% 2.53/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f22])).
% 2.53/1.00  
% 2.53/1.00  fof(f27,plain,(
% 2.53/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(flattening,[],[f26])).
% 2.53/1.00  
% 2.53/1.00  fof(f43,plain,(
% 2.53/1.00    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f44,plain,(
% 2.53/1.00    ! [X0] : ((~v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f43])).
% 2.53/1.00  
% 2.53/1.00  fof(f59,plain,(
% 2.53/1.00    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f44])).
% 2.53/1.00  
% 2.53/1.00  fof(f3,axiom,(
% 2.53/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f23,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f3])).
% 2.53/1.00  
% 2.53/1.00  fof(f56,plain,(
% 2.53/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f23])).
% 2.53/1.00  
% 2.53/1.00  fof(f60,plain,(
% 2.53/1.00    ( ! [X0] : (~v1_xboole_0(sK0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f44])).
% 2.53/1.00  
% 2.53/1.00  fof(f2,axiom,(
% 2.53/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f55,plain,(
% 2.53/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.53/1.00    inference(cnf_transformation,[],[f2])).
% 2.53/1.00  
% 2.53/1.00  fof(f1,axiom,(
% 2.53/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f54,plain,(
% 2.53/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.53/1.00    inference(cnf_transformation,[],[f1])).
% 2.53/1.00  
% 2.53/1.00  cnf(c_26,negated_conjecture,
% 2.53/1.00      ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_12,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | ~ l1_struct_0(X2)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | v1_xboole_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_21,negated_conjecture,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.53/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_232,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.53/1.00      inference(prop_impl,[status(thm)],[c_21]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_18,plain,
% 2.53/1.00      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.53/1.00      | r3_waybel_9(X0,X1,X2)
% 2.53/1.00      | ~ l1_waybel_0(X1,X0)
% 2.53/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.00      | ~ v7_waybel_0(X1)
% 2.53/1.00      | ~ v4_orders_2(X1)
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v2_pre_topc(X0)
% 2.53/1.00      | ~ l1_pre_topc(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_30,negated_conjecture,
% 2.53/1.00      ( v2_pre_topc(sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_537,plain,
% 2.53/1.00      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.53/1.00      | r3_waybel_9(X0,X1,X2)
% 2.53/1.00      | ~ l1_waybel_0(X1,X0)
% 2.53/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.00      | ~ v7_waybel_0(X1)
% 2.53/1.00      | ~ v4_orders_2(X1)
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ l1_pre_topc(X0)
% 2.53/1.00      | sK1 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_538,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.53/1.00      | r3_waybel_9(sK1,X0,X1)
% 2.53/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.53/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.00      | ~ v7_waybel_0(X0)
% 2.53/1.00      | ~ v4_orders_2(X0)
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | ~ l1_pre_topc(sK1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_537]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_31,negated_conjecture,
% 2.53/1.00      ( ~ v2_struct_0(sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_29,negated_conjecture,
% 2.53/1.00      ( l1_pre_topc(sK1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_542,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.53/1.00      | r3_waybel_9(sK1,X0,X1)
% 2.53/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.53/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.00      | ~ v7_waybel_0(X0)
% 2.53/1.00      | ~ v4_orders_2(X0)
% 2.53/1.00      | v2_struct_0(X0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_538,c_31,c_29]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1061,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.53/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.00      | ~ v7_waybel_0(X0)
% 2.53/1.00      | ~ v4_orders_2(X0)
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
% 2.53/1.00      | sK3 != X1
% 2.53/1.00      | sK1 != sK1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_232,c_542]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1062,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.53/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1061]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_23,negated_conjecture,
% 2.53/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1064,plain,
% 2.53/1.00      ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1062,c_23]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1065,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_1064]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1101,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ l1_struct_0(X2)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
% 2.53/1.00      | sK1 != X2 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_1065]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1102,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | ~ l1_struct_0(sK1)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1101]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4,plain,
% 2.53/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_90,plain,
% 2.53/1.00      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1106,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_1102,c_31,c_29,c_90]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_25,negated_conjecture,
% 2.53/1.00      ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1952,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.53/1.00      | sK2 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_1106,c_25]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1953,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(sK2)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1952]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_28,negated_conjecture,
% 2.53/1.00      ( ~ v1_xboole_0(sK2) ),
% 2.53/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1957,plain,
% 2.53/1.00      ( v1_xboole_0(X0)
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1953,c_28]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1958,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_1957]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2301,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.53/1.00      | sK2 != sK2 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_1958]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2857,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_2301]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3337,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.53/1.00      | ~ sP0_iProver_split ),
% 2.53/1.00      inference(splitting,
% 2.53/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.53/1.00                [c_2857]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3698,plain,
% 2.53/1.00      ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.53/1.00      | v1_xboole_0(X0) = iProver_top
% 2.53/1.00      | sP0_iProver_split != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3337]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_9,plain,
% 2.53/1.00      ( ~ l1_pre_topc(X0) | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_612,plain,
% 2.53/1.00      ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) | sK1 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_613,plain,
% 2.53/1.00      ( k2_pre_topc(sK1,k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_612]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_7,plain,
% 2.53/1.00      ( v1_tops_1(X0,X1)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_669,plain,
% 2.53/1.00      ( v1_tops_1(X0,X1)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | k2_pre_topc(X1,X0) != k2_struct_0(X1)
% 2.53/1.00      | sK1 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_670,plain,
% 2.53/1.00      ( v1_tops_1(X0,sK1)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | k2_pre_topc(sK1,X0) != k2_struct_0(sK1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_669]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_11,plain,
% 2.53/1.00      ( ~ v1_tops_1(X0,X1)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ l1_pre_topc(X1)
% 2.53/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_624,plain,
% 2.53/1.00      ( ~ v1_tops_1(X0,X1)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 2.53/1.00      | sK1 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_625,plain,
% 2.53/1.00      ( ~ v1_tops_1(X0,sK1)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | k2_pre_topc(sK1,X0) = u1_struct_0(sK1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_624]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_704,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | k2_pre_topc(sK1,X0) = u1_struct_0(sK1)
% 2.53/1.00      | k2_pre_topc(sK1,X0) != k2_struct_0(sK1) ),
% 2.53/1.00      inference(resolution,[status(thm)],[c_670,c_625]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3705,plain,
% 2.53/1.00      ( k2_pre_topc(sK1,X0) = u1_struct_0(sK1)
% 2.53/1.00      | k2_pre_topc(sK1,X0) != k2_struct_0(sK1)
% 2.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4242,plain,
% 2.53/1.00      ( k2_pre_topc(sK1,k2_struct_0(sK1)) = u1_struct_0(sK1)
% 2.53/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_613,c_3705]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4243,plain,
% 2.53/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1)
% 2.53/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_4242,c_613]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_34,plain,
% 2.53/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_89,plain,
% 2.53/1.00      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_91,plain,
% 2.53/1.00      ( l1_pre_topc(sK1) != iProver_top | l1_struct_0(sK1) = iProver_top ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_89]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3,plain,
% 2.53/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.00      | ~ l1_struct_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_92,plain,
% 2.53/1.00      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.53/1.00      | l1_struct_0(X0) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_94,plain,
% 2.53/1.00      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.53/1.00      | l1_struct_0(sK1) != iProver_top ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_92]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4320,plain,
% 2.53/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_4243,c_34,c_91,c_94]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4559,plain,
% 2.53/1.00      ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.53/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.53/1.00      | v1_xboole_0(X0) = iProver_top
% 2.53/1.00      | sP0_iProver_split != iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_3698,c_4320]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4569,plain,
% 2.53/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.53/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.53/1.00      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
% 2.53/1.00      | sP0_iProver_split != iProver_top ),
% 2.53/1.00      inference(equality_resolution,[status(thm)],[c_4559]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4738,plain,
% 2.53/1.00      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.53/1.00      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
% 2.53/1.00      | sP0_iProver_split != iProver_top ),
% 2.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_4569]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_24,negated_conjecture,
% 2.53/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_39,plain,
% 2.53/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3338,plain,
% 2.53/1.00      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | sP0_iProver_split ),
% 2.53/1.00      inference(splitting,
% 2.53/1.00                [splitting(split),new_symbols(definition,[])],
% 2.53/1.00                [c_2857]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3697,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) != iProver_top
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3) != iProver_top
% 2.53/1.00      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.53/1.00      | sP0_iProver_split = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3338]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_20,plain,
% 2.53/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ l1_struct_0(X1)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 2.53/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_27,negated_conjecture,
% 2.53/1.00      ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f97]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_453,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ l1_struct_0(X1)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.53/1.00      | sK2 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_454,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | ~ l1_struct_0(X0)
% 2.53/1.00      | v1_xboole_0(sK2)
% 2.53/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_453]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_458,plain,
% 2.53/1.00      ( ~ l1_struct_0(X0)
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.53/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.53/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_454,c_28]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_459,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | ~ l1_struct_0(X0)
% 2.53/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_458]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_617,plain,
% 2.53/1.00      ( l1_struct_0(X0) | sK1 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_29]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_618,plain,
% 2.53/1.00      ( l1_struct_0(sK1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_617]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1459,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.53/1.00      | sK1 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_459,c_618]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1460,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1459]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1462,plain,
% 2.53/1.00      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_1460,c_31,c_26,c_25,c_24]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2866,plain,
% 2.53/1.00      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
% 2.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_1462]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3810,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,sK2,sK3) != iProver_top
% 2.53/1.00      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.53/1.00      | sP0_iProver_split = iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_3697,c_2866]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_22,negated_conjecture,
% 2.53/1.00      ( r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.53/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_234,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.53/1.00      inference(prop_impl,[status(thm)],[c_22]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_19,plain,
% 2.53/1.00      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.53/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 2.53/1.00      | ~ l1_waybel_0(X1,X0)
% 2.53/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.00      | ~ v7_waybel_0(X1)
% 2.53/1.00      | ~ v4_orders_2(X1)
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ v2_pre_topc(X0)
% 2.53/1.00      | ~ l1_pre_topc(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_504,plain,
% 2.53/1.00      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.53/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 2.53/1.00      | ~ l1_waybel_0(X1,X0)
% 2.53/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.00      | ~ v7_waybel_0(X1)
% 2.53/1.00      | ~ v4_orders_2(X1)
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ l1_pre_topc(X0)
% 2.53/1.00      | sK1 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_505,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.53/1.00      | ~ r3_waybel_9(sK1,X0,X1)
% 2.53/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.53/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.00      | ~ v7_waybel_0(X0)
% 2.53/1.00      | ~ v4_orders_2(X0)
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | ~ l1_pre_topc(sK1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_504]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_509,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.53/1.00      | ~ r3_waybel_9(sK1,X0,X1)
% 2.53/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.53/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.00      | ~ v7_waybel_0(X0)
% 2.53/1.00      | ~ v4_orders_2(X0)
% 2.53/1.00      | v2_struct_0(X0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_505,c_31,c_29]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1035,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ l1_waybel_0(X0,sK1)
% 2.53/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.00      | ~ v7_waybel_0(X0)
% 2.53/1.00      | ~ v4_orders_2(X0)
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
% 2.53/1.00      | sK3 != X1
% 2.53/1.00      | sK1 != sK1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_234,c_509]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1036,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.53/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1035]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1038,plain,
% 2.53/1.00      ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1036,c_23]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1039,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_1038]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1149,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ l1_struct_0(X2)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
% 2.53/1.00      | sK1 != X2 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_1039]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1150,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | ~ l1_struct_0(sK1)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1149]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1154,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_1150,c_31,c_29,c_90]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1907,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.53/1.00      | sK2 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_1154,c_25]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1908,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(sK2)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1907]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1912,plain,
% 2.53/1.00      ( v1_xboole_0(X0)
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1908,c_28]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1913,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_1912]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2339,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.53/1.00      | sK2 != sK2 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_1913]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2853,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_2339]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3339,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3)
% 2.53/1.00      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | sP0_iProver_split ),
% 2.53/1.00      inference(splitting,
% 2.53/1.00                [splitting(split),new_symbols(definition,[])],
% 2.53/1.00                [c_2853]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3699,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) = iProver_top
% 2.53/1.00      | r1_waybel_7(sK1,sK2,sK3) = iProver_top
% 2.53/1.00      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.53/1.00      | sP0_iProver_split = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3339]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3787,plain,
% 2.53/1.00      ( r1_waybel_7(sK1,sK2,sK3) = iProver_top
% 2.53/1.00      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.53/1.00      | sP0_iProver_split = iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_3699,c_2866]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3816,plain,
% 2.53/1.00      ( v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.53/1.00      | sP0_iProver_split = iProver_top ),
% 2.53/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3810,c_3787]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_14,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | ~ l1_struct_0(X2)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | v1_xboole_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1510,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | sK1 != X2 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_618]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1511,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1510]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1515,plain,
% 2.53/1.00      ( v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1511,c_31]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1516,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_1515]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1847,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.53/1.00      | sK2 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_1516,c_25]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1848,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1847]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1852,plain,
% 2.53/1.00      ( v1_xboole_0(X0)
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1848,c_28]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1853,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_1852]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2400,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.53/1.00      | sK2 != sK2 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_1853]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2845,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_2400]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3879,plain,
% 2.53/1.00      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(k2_struct_0(sK1))
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2845]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3880,plain,
% 2.53/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.53/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.53/1.00      | v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.53/1.00      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3879]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_17,plain,
% 2.53/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.53/1.00      | ~ l1_struct_0(X2)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | v1_xboole_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_15,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.53/1.00      | ~ l1_struct_0(X2)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | v1_xboole_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_177,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.53/1.00      | ~ l1_struct_0(X2)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | v1_xboole_0(X0) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_17,c_15]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_178,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.53/1.00      | ~ l1_struct_0(X2)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_177]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1477,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | sK1 != X2 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_178,c_618]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1478,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1477]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1482,plain,
% 2.53/1.00      ( ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1478,c_31]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1483,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_1482]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1877,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.53/1.00      | sK2 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_1483,c_25]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1878,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(sK2)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1877]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1882,plain,
% 2.53/1.00      ( v1_xboole_0(X0)
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1878,c_28]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1883,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_1882]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2377,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.53/1.00      | sK2 != sK2 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_1883]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2849,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_2377]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3885,plain,
% 2.53/1.00      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 2.53/1.00      | ~ v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(k2_struct_0(sK1))
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2849]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3886,plain,
% 2.53/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.53/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.53/1.00      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top
% 2.53/1.00      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3885]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_16,plain,
% 2.53/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.53/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | ~ l1_struct_0(X2)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | v1_xboole_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_414,plain,
% 2.53/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.53/1.00      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.53/1.00      | v2_struct_0(X2)
% 2.53/1.00      | ~ l1_struct_0(X2)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(X1)
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.53/1.00      | sK2 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_415,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ l1_struct_0(X1)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | v1_xboole_0(sK2)
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_414]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_419,plain,
% 2.53/1.00      ( v1_xboole_0(X0)
% 2.53/1.00      | ~ l1_struct_0(X1)
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_415,c_28]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_420,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | ~ l1_struct_0(X1)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_419]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1550,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 2.53/1.00      | v2_struct_0(X1)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | sK1 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_420,c_618]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1551,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_1550]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1555,plain,
% 2.53/1.00      ( v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.53/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1551,c_31]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1556,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_1555]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1997,plain,
% 2.53/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | sK2 != sK2 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_1556]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2275,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.53/1.00      | sK2 != sK2 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_1997]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2861,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.53/1.00      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.53/1.00      | v1_xboole_0(X0)
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.53/1.00      inference(equality_resolution_simp,[status(thm)],[c_2275]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3891,plain,
% 2.53/1.00      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 2.53/1.00      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.53/1.00      | v1_xboole_0(k2_struct_0(sK1))
% 2.53/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2861]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3892,plain,
% 2.53/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.53/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.53/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.53/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.53/1.00      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top
% 2.53/1.00      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3891]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3341,plain,( X0 = X0 ),theory(equality) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4101,plain,
% 2.53/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) = k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_3341]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_6,plain,
% 2.53/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | ~ v2_pre_topc(X0)
% 2.53/1.00      | ~ l1_pre_topc(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_570,plain,
% 2.53/1.00      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.00      | v2_struct_0(X0)
% 2.53/1.00      | ~ l1_pre_topc(X0)
% 2.53/1.00      | sK1 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_30]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_571,plain,
% 2.53/1.00      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | ~ l1_pre_topc(sK1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_570]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_84,plain,
% 2.53/1.00      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.00      | v2_struct_0(sK1)
% 2.53/1.00      | ~ v2_pre_topc(sK1)
% 2.53/1.00      | ~ l1_pre_topc(sK1) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_573,plain,
% 2.53/1.00      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_571,c_31,c_30,c_29,c_84]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3707,plain,
% 2.53/1.00      ( m1_subset_1(sK0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2,plain,
% 2.53/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.53/1.00      | ~ v1_xboole_0(X1)
% 2.53/1.00      | v1_xboole_0(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3712,plain,
% 2.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.53/1.00      | v1_xboole_0(X1) != iProver_top
% 2.53/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4111,plain,
% 2.53/1.00      ( v1_xboole_0(sK0(sK1)) = iProver_top
% 2.53/1.00      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.53/1.00      inference(superposition,[status(thm)],[c_3707,c_3712]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_32,plain,
% 2.53/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_33,plain,
% 2.53/1.00      ( v2_pre_topc(sK1) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_5,plain,
% 2.53/1.00      ( v2_struct_0(X0)
% 2.53/1.00      | ~ v2_pre_topc(X0)
% 2.53/1.00      | ~ l1_pre_topc(X0)
% 2.53/1.00      | ~ v1_xboole_0(sK0(X0)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_86,plain,
% 2.53/1.00      ( v2_struct_0(X0) = iProver_top
% 2.53/1.00      | v2_pre_topc(X0) != iProver_top
% 2.53/1.00      | l1_pre_topc(X0) != iProver_top
% 2.53/1.00      | v1_xboole_0(sK0(X0)) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_88,plain,
% 2.53/1.00      ( v2_struct_0(sK1) = iProver_top
% 2.53/1.00      | v2_pre_topc(sK1) != iProver_top
% 2.53/1.00      | l1_pre_topc(sK1) != iProver_top
% 2.53/1.00      | v1_xboole_0(sK0(sK1)) != iProver_top ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_86]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4144,plain,
% 2.53/1.00      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_4111,c_32,c_33,c_34,c_88]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4325,plain,
% 2.53/1.00      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 2.53/1.00      inference(demodulation,[status(thm)],[c_4320,c_4144]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4666,plain,
% 2.53/1.00      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) = u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_3341]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4740,plain,
% 2.53/1.00      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_4738,c_34,c_39,c_91,c_94,c_3816,c_3880,c_3886,c_3892,
% 2.53/1.00                 c_4101,c_4325,c_4569,c_4666]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1,plain,
% 2.53/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3713,plain,
% 2.53/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_0,plain,
% 2.53/1.00      ( k2_subset_1(X0) = X0 ),
% 2.53/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3726,plain,
% 2.53/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.53/1.00      inference(light_normalisation,[status(thm)],[c_3713,c_0]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4745,plain,
% 2.53/1.00      ( $false ),
% 2.53/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4740,c_3726]) ).
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/1.00  
% 2.53/1.00  ------                               Statistics
% 2.53/1.00  
% 2.53/1.00  ------ General
% 2.53/1.00  
% 2.53/1.00  abstr_ref_over_cycles:                  0
% 2.53/1.00  abstr_ref_under_cycles:                 0
% 2.53/1.00  gc_basic_clause_elim:                   0
% 2.53/1.00  forced_gc_time:                         0
% 2.53/1.00  parsing_time:                           0.011
% 2.53/1.00  unif_index_cands_time:                  0.
% 2.53/1.00  unif_index_add_time:                    0.
% 2.53/1.00  orderings_time:                         0.
% 2.53/1.00  out_proof_time:                         0.029
% 2.53/1.00  total_time:                             0.229
% 2.53/1.00  num_of_symbols:                         60
% 2.53/1.00  num_of_terms:                           2145
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing
% 2.53/1.00  
% 2.53/1.00  num_of_splits:                          2
% 2.53/1.00  num_of_split_atoms:                     1
% 2.53/1.00  num_of_reused_defs:                     1
% 2.53/1.00  num_eq_ax_congr_red:                    10
% 2.53/1.00  num_of_sem_filtered_clauses:            1
% 2.53/1.00  num_of_subtypes:                        0
% 2.53/1.00  monotx_restored_types:                  0
% 2.53/1.00  sat_num_of_epr_types:                   0
% 2.53/1.00  sat_num_of_non_cyclic_types:            0
% 2.53/1.00  sat_guarded_non_collapsed_types:        0
% 2.53/1.00  num_pure_diseq_elim:                    0
% 2.53/1.00  simp_replaced_by:                       0
% 2.53/1.00  res_preprocessed:                       125
% 2.53/1.00  prep_upred:                             0
% 2.53/1.00  prep_unflattend:                        36
% 2.53/1.00  smt_new_axioms:                         0
% 2.53/1.00  pred_elim_cands:                        6
% 2.53/1.00  pred_elim:                              9
% 2.53/1.00  pred_elim_cl:                           12
% 2.53/1.00  pred_elim_cycles:                       24
% 2.53/1.00  merged_defs:                            2
% 2.53/1.00  merged_defs_ncl:                        0
% 2.53/1.00  bin_hyper_res:                          2
% 2.53/1.00  prep_cycles:                            4
% 2.53/1.00  pred_elim_time:                         0.1
% 2.53/1.00  splitting_time:                         0.
% 2.53/1.00  sem_filter_time:                        0.
% 2.53/1.00  monotx_time:                            0.
% 2.53/1.00  subtype_inf_time:                       0.
% 2.53/1.00  
% 2.53/1.00  ------ Problem properties
% 2.53/1.00  
% 2.53/1.00  clauses:                                21
% 2.53/1.00  conjectures:                            4
% 2.53/1.00  epr:                                    2
% 2.53/1.00  horn:                                   17
% 2.53/1.00  ground:                                 11
% 2.53/1.00  unary:                                  11
% 2.53/1.00  binary:                                 0
% 2.53/1.00  lits:                                   60
% 2.53/1.00  lits_eq:                                15
% 2.53/1.00  fd_pure:                                0
% 2.53/1.00  fd_pseudo:                              0
% 2.53/1.00  fd_cond:                                0
% 2.53/1.00  fd_pseudo_cond:                         0
% 2.53/1.00  ac_symbols:                             0
% 2.53/1.00  
% 2.53/1.00  ------ Propositional Solver
% 2.53/1.00  
% 2.53/1.00  prop_solver_calls:                      26
% 2.53/1.00  prop_fast_solver_calls:                 1788
% 2.53/1.00  smt_solver_calls:                       0
% 2.53/1.00  smt_fast_solver_calls:                  0
% 2.53/1.00  prop_num_of_clauses:                    940
% 2.53/1.00  prop_preprocess_simplified:             3731
% 2.53/1.00  prop_fo_subsumed:                       45
% 2.53/1.00  prop_solver_time:                       0.
% 2.53/1.00  smt_solver_time:                        0.
% 2.53/1.00  smt_fast_solver_time:                   0.
% 2.53/1.00  prop_fast_solver_time:                  0.
% 2.53/1.00  prop_unsat_core_time:                   0.
% 2.53/1.00  
% 2.53/1.00  ------ QBF
% 2.53/1.00  
% 2.53/1.00  qbf_q_res:                              0
% 2.53/1.00  qbf_num_tautologies:                    0
% 2.53/1.00  qbf_prep_cycles:                        0
% 2.53/1.00  
% 2.53/1.00  ------ BMC1
% 2.53/1.00  
% 2.53/1.00  bmc1_current_bound:                     -1
% 2.53/1.00  bmc1_last_solved_bound:                 -1
% 2.53/1.00  bmc1_unsat_core_size:                   -1
% 2.53/1.00  bmc1_unsat_core_parents_size:           -1
% 2.53/1.00  bmc1_merge_next_fun:                    0
% 2.53/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.53/1.00  
% 2.53/1.00  ------ Instantiation
% 2.53/1.00  
% 2.53/1.00  inst_num_of_clauses:                    202
% 2.53/1.00  inst_num_in_passive:                    27
% 2.53/1.00  inst_num_in_active:                     133
% 2.53/1.00  inst_num_in_unprocessed:                42
% 2.53/1.00  inst_num_of_loops:                      140
% 2.53/1.00  inst_num_of_learning_restarts:          0
% 2.53/1.00  inst_num_moves_active_passive:          5
% 2.53/1.00  inst_lit_activity:                      0
% 2.53/1.00  inst_lit_activity_moves:                0
% 2.53/1.00  inst_num_tautologies:                   0
% 2.53/1.00  inst_num_prop_implied:                  0
% 2.53/1.00  inst_num_existing_simplified:           0
% 2.53/1.00  inst_num_eq_res_simplified:             0
% 2.53/1.00  inst_num_child_elim:                    0
% 2.53/1.00  inst_num_of_dismatching_blockings:      32
% 2.53/1.00  inst_num_of_non_proper_insts:           148
% 2.53/1.00  inst_num_of_duplicates:                 0
% 2.53/1.00  inst_inst_num_from_inst_to_res:         0
% 2.53/1.00  inst_dismatching_checking_time:         0.
% 2.53/1.00  
% 2.53/1.00  ------ Resolution
% 2.53/1.00  
% 2.53/1.00  res_num_of_clauses:                     0
% 2.53/1.00  res_num_in_passive:                     0
% 2.53/1.00  res_num_in_active:                      0
% 2.53/1.00  res_num_of_loops:                       129
% 2.53/1.00  res_forward_subset_subsumed:            19
% 2.53/1.00  res_backward_subset_subsumed:           0
% 2.53/1.00  res_forward_subsumed:                   1
% 2.53/1.00  res_backward_subsumed:                  0
% 2.53/1.00  res_forward_subsumption_resolution:     2
% 2.53/1.00  res_backward_subsumption_resolution:    0
% 2.53/1.00  res_clause_to_clause_subsumption:       364
% 2.53/1.00  res_orphan_elimination:                 0
% 2.53/1.00  res_tautology_del:                      31
% 2.53/1.00  res_num_eq_res_simplified:              6
% 2.53/1.00  res_num_sel_changes:                    0
% 2.53/1.00  res_moves_from_active_to_pass:          0
% 2.53/1.00  
% 2.53/1.00  ------ Superposition
% 2.53/1.00  
% 2.53/1.00  sup_time_total:                         0.
% 2.53/1.00  sup_time_generating:                    0.
% 2.53/1.00  sup_time_sim_full:                      0.
% 2.53/1.00  sup_time_sim_immed:                     0.
% 2.53/1.00  
% 2.53/1.00  sup_num_of_clauses:                     22
% 2.53/1.00  sup_num_in_active:                      20
% 2.53/1.00  sup_num_in_passive:                     2
% 2.53/1.00  sup_num_of_loops:                       26
% 2.53/1.00  sup_fw_superposition:                   6
% 2.53/1.00  sup_bw_superposition:                   1
% 2.53/1.00  sup_immediate_simplified:               4
% 2.53/1.00  sup_given_eliminated:                   0
% 2.53/1.00  comparisons_done:                       0
% 2.53/1.00  comparisons_avoided:                    0
% 2.53/1.00  
% 2.53/1.00  ------ Simplifications
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  sim_fw_subset_subsumed:                 2
% 2.53/1.00  sim_bw_subset_subsumed:                 1
% 2.53/1.00  sim_fw_subsumed:                        1
% 2.53/1.00  sim_bw_subsumed:                        1
% 2.53/1.00  sim_fw_subsumption_res:                 2
% 2.53/1.00  sim_bw_subsumption_res:                 0
% 2.53/1.00  sim_tautology_del:                      2
% 2.53/1.00  sim_eq_tautology_del:                   0
% 2.53/1.00  sim_eq_res_simp:                        1
% 2.53/1.00  sim_fw_demodulated:                     0
% 2.53/1.00  sim_bw_demodulated:                     6
% 2.53/1.00  sim_light_normalised:                   8
% 2.53/1.00  sim_joinable_taut:                      0
% 2.53/1.00  sim_joinable_simp:                      0
% 2.53/1.00  sim_ac_normalised:                      0
% 2.53/1.00  sim_smt_subsumption:                    0
% 2.53/1.00  
%------------------------------------------------------------------------------
