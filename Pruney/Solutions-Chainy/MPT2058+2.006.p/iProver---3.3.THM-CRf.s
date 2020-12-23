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
% DateTime   : Thu Dec  3 12:29:15 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  208 (1796 expanded)
%              Number of clauses        :  131 ( 378 expanded)
%              Number of leaves         :   15 ( 498 expanded)
%              Depth                    :   36
%              Number of atoms          : 1383 (15921 expanded)
%              Number of equality atoms :  196 ( 419 expanded)
%              Maximal formula depth    :   16 (   8 average)
%              Maximal clause size      :   26 (   7 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(nnf_transformation,[],[f33])).

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

fof(f67,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f67,f52])).

fof(f7,axiom,(
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

fof(f16,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
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
    inference(definition_unfolding,[],[f54,f52,f52,f52])).

fof(f72,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

fof(f60,plain,(
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

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f68,f52])).

fof(f65,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f8])).

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
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
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
    inference(definition_unfolding,[],[f56,f52,f52,f52])).

fof(f9,axiom,(
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

fof(f17,plain,(
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
    inference(pure_predicate_removal,[],[f9])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
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
    inference(definition_unfolding,[],[f58,f52,f52,f52,f52])).

fof(f66,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f66,f52])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
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
    inference(definition_unfolding,[],[f53,f52,f52,f52])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f52,f52,f52,f52])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f69,f52])).

fof(f71,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
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

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3881,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_22,negated_conjecture,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_8,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17,negated_conjecture,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_209,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_493,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_494,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_498,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_27,c_25])).

cnf(c_871,plain,
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
    inference(resolution_lifted,[status(thm)],[c_209,c_498])).

cnf(c_872,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_871])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_874,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_872,c_19])).

cnf(c_875,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_874])).

cnf(c_911,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_875])).

cnf(c_912,plain,
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
    inference(unflattening,[status(thm)],[c_911])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_68,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_916,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_912,c_27,c_25,c_68])).

cnf(c_917,plain,
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
    inference(renaming,[status(thm)],[c_916])).

cnf(c_21,negated_conjecture,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1505,plain,
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
    inference(resolution_lifted,[status(thm)],[c_917,c_21])).

cnf(c_1506,plain,
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
    inference(unflattening,[status(thm)],[c_1505])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1510,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1506,c_24])).

cnf(c_1511,plain,
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
    inference(renaming,[status(thm)],[c_1510])).

cnf(c_1854,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_1511])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_542,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_543,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_1020,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_543])).

cnf(c_1021,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_1020])).

cnf(c_65,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1023,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1021,c_27,c_25,c_65,c_68])).

cnf(c_2558,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1854,c_1023])).

cnf(c_2559,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2558])).

cnf(c_10,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1036,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_543])).

cnf(c_1037,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1036])).

cnf(c_1041,plain,
    ( v4_orders_2(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1037,c_27])).

cnf(c_1042,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1041])).

cnf(c_1430,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1042,c_21])).

cnf(c_1431,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1430])).

cnf(c_1435,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1431,c_24])).

cnf(c_1436,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1435])).

cnf(c_1930,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1436])).

cnf(c_2511,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1930,c_1023])).

cnf(c_2512,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v4_orders_2(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2511])).

cnf(c_2812,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_2559,c_2512])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_23,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_370,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_371,plain,
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
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_375,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_371,c_24])).

cnf(c_376,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_375])).

cnf(c_1102,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_376,c_543])).

cnf(c_1103,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1102])).

cnf(c_1107,plain,
    ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1103,c_27])).

cnf(c_1108,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1107])).

cnf(c_1550,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1108])).

cnf(c_1828,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1550])).

cnf(c_2589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1828,c_1023])).

cnf(c_2590,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v7_waybel_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_2589])).

cnf(c_3073,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_2812,c_2590])).

cnf(c_9,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1069,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_543])).

cnf(c_1070,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1069])).

cnf(c_1074,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1070,c_27])).

cnf(c_1075,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1074])).

cnf(c_1400,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1075,c_21])).

cnf(c_1401,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1400])).

cnf(c_1405,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1401,c_24])).

cnf(c_1406,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1405])).

cnf(c_1953,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1406])).

cnf(c_2495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1953,c_1023])).

cnf(c_2496,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v2_struct_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2495])).

cnf(c_3376,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_3073,c_2496])).

cnf(c_3875,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
    | r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3376])).

cnf(c_5,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1031,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_543])).

cnf(c_1032,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1031])).

cnf(c_16,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_409,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_410,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_414,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_24])).

cnf(c_415,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(renaming,[status(thm)],[c_414])).

cnf(c_1009,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_415,c_543])).

cnf(c_1010,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_1009])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1012,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1010,c_27,c_22,c_21,c_20])).

cnf(c_3482,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_1012])).

cnf(c_3943,plain,
    ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3875,c_1032,c_3482])).

cnf(c_3944,plain,
    ( r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3943])).

cnf(c_3878,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_211,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_460,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_461,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_465,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_27,c_25])).

cnf(c_845,plain,
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
    inference(resolution_lifted,[status(thm)],[c_211,c_465])).

cnf(c_846,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_845])).

cnf(c_848,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,sK1,sK2)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_846,c_19])).

cnf(c_849,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_848])).

cnf(c_959,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_849])).

cnf(c_960,plain,
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
    inference(unflattening,[status(thm)],[c_959])).

cnf(c_964,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_960,c_27,c_25,c_68])).

cnf(c_965,plain,
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
    inference(renaming,[status(thm)],[c_964])).

cnf(c_1460,plain,
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
    inference(resolution_lifted,[status(thm)],[c_965,c_21])).

cnf(c_1461,plain,
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
    inference(unflattening,[status(thm)],[c_1460])).

cnf(c_1465,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1461,c_24])).

cnf(c_1466,plain,
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
    inference(renaming,[status(thm)],[c_1465])).

cnf(c_1892,plain,
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
    inference(resolution_lifted,[status(thm)],[c_22,c_1466])).

cnf(c_2527,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1892,c_1023])).

cnf(c_2528,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2527])).

cnf(c_2839,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_2528,c_2512])).

cnf(c_3046,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_2839,c_2590])).

cnf(c_3400,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_3046,c_2496])).

cnf(c_3874,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3400])).

cnf(c_3935,plain,
    ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3874,c_1032,c_3482])).

cnf(c_3936,plain,
    ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3935])).

cnf(c_3940,plain,
    ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3936,c_3878])).

cnf(c_3948,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3944,c_3878,c_3940])).

cnf(c_4171,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3881,c_3948])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3882,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4265,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4171,c_3882])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.84/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/0.99  
% 1.84/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.84/0.99  
% 1.84/0.99  ------  iProver source info
% 1.84/0.99  
% 1.84/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.84/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.84/0.99  git: non_committed_changes: false
% 1.84/0.99  git: last_make_outside_of_git: false
% 1.84/0.99  
% 1.84/0.99  ------ 
% 1.84/0.99  
% 1.84/0.99  ------ Input Options
% 1.84/0.99  
% 1.84/0.99  --out_options                           all
% 1.84/0.99  --tptp_safe_out                         true
% 1.84/0.99  --problem_path                          ""
% 1.84/0.99  --include_path                          ""
% 1.84/0.99  --clausifier                            res/vclausify_rel
% 1.84/0.99  --clausifier_options                    --mode clausify
% 1.84/0.99  --stdin                                 false
% 1.84/0.99  --stats_out                             all
% 1.84/0.99  
% 1.84/0.99  ------ General Options
% 1.84/0.99  
% 1.84/0.99  --fof                                   false
% 1.84/0.99  --time_out_real                         305.
% 1.84/0.99  --time_out_virtual                      -1.
% 1.84/0.99  --symbol_type_check                     false
% 1.84/0.99  --clausify_out                          false
% 1.84/0.99  --sig_cnt_out                           false
% 1.84/0.99  --trig_cnt_out                          false
% 1.84/0.99  --trig_cnt_out_tolerance                1.
% 1.84/0.99  --trig_cnt_out_sk_spl                   false
% 1.84/0.99  --abstr_cl_out                          false
% 1.84/0.99  
% 1.84/0.99  ------ Global Options
% 1.84/0.99  
% 1.84/0.99  --schedule                              default
% 1.84/0.99  --add_important_lit                     false
% 1.84/0.99  --prop_solver_per_cl                    1000
% 1.84/0.99  --min_unsat_core                        false
% 1.84/0.99  --soft_assumptions                      false
% 1.84/0.99  --soft_lemma_size                       3
% 1.84/0.99  --prop_impl_unit_size                   0
% 1.84/0.99  --prop_impl_unit                        []
% 1.84/0.99  --share_sel_clauses                     true
% 1.84/0.99  --reset_solvers                         false
% 1.84/0.99  --bc_imp_inh                            [conj_cone]
% 1.84/0.99  --conj_cone_tolerance                   3.
% 1.84/0.99  --extra_neg_conj                        none
% 1.84/0.99  --large_theory_mode                     true
% 1.84/0.99  --prolific_symb_bound                   200
% 1.84/0.99  --lt_threshold                          2000
% 1.84/0.99  --clause_weak_htbl                      true
% 1.84/0.99  --gc_record_bc_elim                     false
% 1.84/0.99  
% 1.84/0.99  ------ Preprocessing Options
% 1.84/0.99  
% 1.84/0.99  --preprocessing_flag                    true
% 1.84/0.99  --time_out_prep_mult                    0.1
% 1.84/0.99  --splitting_mode                        input
% 1.84/0.99  --splitting_grd                         true
% 1.84/0.99  --splitting_cvd                         false
% 1.84/0.99  --splitting_cvd_svl                     false
% 1.84/0.99  --splitting_nvd                         32
% 1.84/0.99  --sub_typing                            true
% 1.84/0.99  --prep_gs_sim                           true
% 1.84/0.99  --prep_unflatten                        true
% 1.84/0.99  --prep_res_sim                          true
% 1.84/0.99  --prep_upred                            true
% 1.84/0.99  --prep_sem_filter                       exhaustive
% 1.84/0.99  --prep_sem_filter_out                   false
% 1.84/0.99  --pred_elim                             true
% 1.84/0.99  --res_sim_input                         true
% 1.84/0.99  --eq_ax_congr_red                       true
% 1.84/0.99  --pure_diseq_elim                       true
% 1.84/0.99  --brand_transform                       false
% 1.84/0.99  --non_eq_to_eq                          false
% 1.84/0.99  --prep_def_merge                        true
% 1.84/0.99  --prep_def_merge_prop_impl              false
% 1.84/0.99  --prep_def_merge_mbd                    true
% 1.84/0.99  --prep_def_merge_tr_red                 false
% 1.84/0.99  --prep_def_merge_tr_cl                  false
% 1.84/0.99  --smt_preprocessing                     true
% 1.84/0.99  --smt_ac_axioms                         fast
% 1.84/0.99  --preprocessed_out                      false
% 1.84/0.99  --preprocessed_stats                    false
% 1.84/0.99  
% 1.84/0.99  ------ Abstraction refinement Options
% 1.84/0.99  
% 1.84/0.99  --abstr_ref                             []
% 1.84/0.99  --abstr_ref_prep                        false
% 1.84/0.99  --abstr_ref_until_sat                   false
% 1.84/0.99  --abstr_ref_sig_restrict                funpre
% 1.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/0.99  --abstr_ref_under                       []
% 1.84/0.99  
% 1.84/0.99  ------ SAT Options
% 1.84/0.99  
% 1.84/0.99  --sat_mode                              false
% 1.84/0.99  --sat_fm_restart_options                ""
% 1.84/0.99  --sat_gr_def                            false
% 1.84/0.99  --sat_epr_types                         true
% 1.84/0.99  --sat_non_cyclic_types                  false
% 1.84/0.99  --sat_finite_models                     false
% 1.84/0.99  --sat_fm_lemmas                         false
% 1.84/0.99  --sat_fm_prep                           false
% 1.84/0.99  --sat_fm_uc_incr                        true
% 1.84/0.99  --sat_out_model                         small
% 1.84/0.99  --sat_out_clauses                       false
% 1.84/0.99  
% 1.84/0.99  ------ QBF Options
% 1.84/0.99  
% 1.84/0.99  --qbf_mode                              false
% 1.84/0.99  --qbf_elim_univ                         false
% 1.84/0.99  --qbf_dom_inst                          none
% 1.84/0.99  --qbf_dom_pre_inst                      false
% 1.84/0.99  --qbf_sk_in                             false
% 1.84/0.99  --qbf_pred_elim                         true
% 1.84/0.99  --qbf_split                             512
% 1.84/0.99  
% 1.84/0.99  ------ BMC1 Options
% 1.84/0.99  
% 1.84/0.99  --bmc1_incremental                      false
% 1.84/0.99  --bmc1_axioms                           reachable_all
% 1.84/0.99  --bmc1_min_bound                        0
% 1.84/0.99  --bmc1_max_bound                        -1
% 1.84/0.99  --bmc1_max_bound_default                -1
% 1.84/0.99  --bmc1_symbol_reachability              true
% 1.84/0.99  --bmc1_property_lemmas                  false
% 1.84/0.99  --bmc1_k_induction                      false
% 1.84/0.99  --bmc1_non_equiv_states                 false
% 1.84/0.99  --bmc1_deadlock                         false
% 1.84/0.99  --bmc1_ucm                              false
% 1.84/0.99  --bmc1_add_unsat_core                   none
% 1.84/0.99  --bmc1_unsat_core_children              false
% 1.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/0.99  --bmc1_out_stat                         full
% 1.84/0.99  --bmc1_ground_init                      false
% 1.84/0.99  --bmc1_pre_inst_next_state              false
% 1.84/0.99  --bmc1_pre_inst_state                   false
% 1.84/0.99  --bmc1_pre_inst_reach_state             false
% 1.84/0.99  --bmc1_out_unsat_core                   false
% 1.84/0.99  --bmc1_aig_witness_out                  false
% 1.84/0.99  --bmc1_verbose                          false
% 1.84/0.99  --bmc1_dump_clauses_tptp                false
% 1.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.84/0.99  --bmc1_dump_file                        -
% 1.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.84/0.99  --bmc1_ucm_extend_mode                  1
% 1.84/0.99  --bmc1_ucm_init_mode                    2
% 1.84/0.99  --bmc1_ucm_cone_mode                    none
% 1.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.84/0.99  --bmc1_ucm_relax_model                  4
% 1.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/0.99  --bmc1_ucm_layered_model                none
% 1.84/0.99  --bmc1_ucm_max_lemma_size               10
% 1.84/0.99  
% 1.84/0.99  ------ AIG Options
% 1.84/0.99  
% 1.84/0.99  --aig_mode                              false
% 1.84/0.99  
% 1.84/0.99  ------ Instantiation Options
% 1.84/0.99  
% 1.84/0.99  --instantiation_flag                    true
% 1.84/0.99  --inst_sos_flag                         false
% 1.84/0.99  --inst_sos_phase                        true
% 1.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/0.99  --inst_lit_sel_side                     num_symb
% 1.84/0.99  --inst_solver_per_active                1400
% 1.84/0.99  --inst_solver_calls_frac                1.
% 1.84/0.99  --inst_passive_queue_type               priority_queues
% 1.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/0.99  --inst_passive_queues_freq              [25;2]
% 1.84/0.99  --inst_dismatching                      true
% 1.84/0.99  --inst_eager_unprocessed_to_passive     true
% 1.84/0.99  --inst_prop_sim_given                   true
% 1.84/0.99  --inst_prop_sim_new                     false
% 1.84/0.99  --inst_subs_new                         false
% 1.84/0.99  --inst_eq_res_simp                      false
% 1.84/0.99  --inst_subs_given                       false
% 1.84/0.99  --inst_orphan_elimination               true
% 1.84/0.99  --inst_learning_loop_flag               true
% 1.84/0.99  --inst_learning_start                   3000
% 1.84/0.99  --inst_learning_factor                  2
% 1.84/0.99  --inst_start_prop_sim_after_learn       3
% 1.84/0.99  --inst_sel_renew                        solver
% 1.84/0.99  --inst_lit_activity_flag                true
% 1.84/0.99  --inst_restr_to_given                   false
% 1.84/0.99  --inst_activity_threshold               500
% 1.84/0.99  --inst_out_proof                        true
% 1.84/0.99  
% 1.84/0.99  ------ Resolution Options
% 1.84/0.99  
% 1.84/0.99  --resolution_flag                       true
% 1.84/0.99  --res_lit_sel                           adaptive
% 1.84/0.99  --res_lit_sel_side                      none
% 1.84/0.99  --res_ordering                          kbo
% 1.84/0.99  --res_to_prop_solver                    active
% 1.84/0.99  --res_prop_simpl_new                    false
% 1.84/0.99  --res_prop_simpl_given                  true
% 1.84/0.99  --res_passive_queue_type                priority_queues
% 1.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/0.99  --res_passive_queues_freq               [15;5]
% 1.84/0.99  --res_forward_subs                      full
% 1.84/0.99  --res_backward_subs                     full
% 1.84/0.99  --res_forward_subs_resolution           true
% 1.84/0.99  --res_backward_subs_resolution          true
% 1.84/0.99  --res_orphan_elimination                true
% 1.84/0.99  --res_time_limit                        2.
% 1.84/0.99  --res_out_proof                         true
% 1.84/0.99  
% 1.84/0.99  ------ Superposition Options
% 1.84/0.99  
% 1.84/0.99  --superposition_flag                    true
% 1.84/0.99  --sup_passive_queue_type                priority_queues
% 1.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.84/0.99  --demod_completeness_check              fast
% 1.84/0.99  --demod_use_ground                      true
% 1.84/0.99  --sup_to_prop_solver                    passive
% 1.84/0.99  --sup_prop_simpl_new                    true
% 1.84/0.99  --sup_prop_simpl_given                  true
% 1.84/0.99  --sup_fun_splitting                     false
% 1.84/0.99  --sup_smt_interval                      50000
% 1.84/0.99  
% 1.84/0.99  ------ Superposition Simplification Setup
% 1.84/0.99  
% 1.84/0.99  --sup_indices_passive                   []
% 1.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_full_bw                           [BwDemod]
% 1.84/0.99  --sup_immed_triv                        [TrivRules]
% 1.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_immed_bw_main                     []
% 1.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.99  
% 1.84/0.99  ------ Combination Options
% 1.84/0.99  
% 1.84/0.99  --comb_res_mult                         3
% 1.84/0.99  --comb_sup_mult                         2
% 1.84/0.99  --comb_inst_mult                        10
% 1.84/0.99  
% 1.84/0.99  ------ Debug Options
% 1.84/0.99  
% 1.84/0.99  --dbg_backtrace                         false
% 1.84/0.99  --dbg_dump_prop_clauses                 false
% 1.84/0.99  --dbg_dump_prop_clauses_file            -
% 1.84/0.99  --dbg_out_stat                          false
% 1.84/0.99  ------ Parsing...
% 1.84/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.84/0.99  
% 1.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.84/0.99  
% 1.84/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.84/0.99  
% 1.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.84/0.99  ------ Proving...
% 1.84/0.99  ------ Problem Properties 
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  clauses                                 12
% 1.84/0.99  conjectures                             2
% 1.84/0.99  EPR                                     2
% 1.84/0.99  Horn                                    10
% 1.84/0.99  unary                                   5
% 1.84/0.99  binary                                  2
% 1.84/0.99  lits                                    40
% 1.84/0.99  lits eq                                 15
% 1.84/0.99  fd_pure                                 0
% 1.84/0.99  fd_pseudo                               0
% 1.84/0.99  fd_cond                                 0
% 1.84/0.99  fd_pseudo_cond                          1
% 1.84/0.99  AC symbols                              0
% 1.84/0.99  
% 1.84/0.99  ------ Schedule dynamic 5 is on 
% 1.84/0.99  
% 1.84/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  ------ 
% 1.84/0.99  Current options:
% 1.84/0.99  ------ 
% 1.84/0.99  
% 1.84/0.99  ------ Input Options
% 1.84/0.99  
% 1.84/0.99  --out_options                           all
% 1.84/0.99  --tptp_safe_out                         true
% 1.84/0.99  --problem_path                          ""
% 1.84/0.99  --include_path                          ""
% 1.84/0.99  --clausifier                            res/vclausify_rel
% 1.84/0.99  --clausifier_options                    --mode clausify
% 1.84/0.99  --stdin                                 false
% 1.84/0.99  --stats_out                             all
% 1.84/0.99  
% 1.84/0.99  ------ General Options
% 1.84/0.99  
% 1.84/0.99  --fof                                   false
% 1.84/0.99  --time_out_real                         305.
% 1.84/0.99  --time_out_virtual                      -1.
% 1.84/0.99  --symbol_type_check                     false
% 1.84/0.99  --clausify_out                          false
% 1.84/0.99  --sig_cnt_out                           false
% 1.84/0.99  --trig_cnt_out                          false
% 1.84/0.99  --trig_cnt_out_tolerance                1.
% 1.84/0.99  --trig_cnt_out_sk_spl                   false
% 1.84/0.99  --abstr_cl_out                          false
% 1.84/0.99  
% 1.84/0.99  ------ Global Options
% 1.84/0.99  
% 1.84/0.99  --schedule                              default
% 1.84/0.99  --add_important_lit                     false
% 1.84/0.99  --prop_solver_per_cl                    1000
% 1.84/0.99  --min_unsat_core                        false
% 1.84/0.99  --soft_assumptions                      false
% 1.84/0.99  --soft_lemma_size                       3
% 1.84/0.99  --prop_impl_unit_size                   0
% 1.84/0.99  --prop_impl_unit                        []
% 1.84/0.99  --share_sel_clauses                     true
% 1.84/0.99  --reset_solvers                         false
% 1.84/0.99  --bc_imp_inh                            [conj_cone]
% 1.84/0.99  --conj_cone_tolerance                   3.
% 1.84/0.99  --extra_neg_conj                        none
% 1.84/0.99  --large_theory_mode                     true
% 1.84/0.99  --prolific_symb_bound                   200
% 1.84/0.99  --lt_threshold                          2000
% 1.84/0.99  --clause_weak_htbl                      true
% 1.84/0.99  --gc_record_bc_elim                     false
% 1.84/0.99  
% 1.84/0.99  ------ Preprocessing Options
% 1.84/0.99  
% 1.84/0.99  --preprocessing_flag                    true
% 1.84/0.99  --time_out_prep_mult                    0.1
% 1.84/0.99  --splitting_mode                        input
% 1.84/0.99  --splitting_grd                         true
% 1.84/0.99  --splitting_cvd                         false
% 1.84/0.99  --splitting_cvd_svl                     false
% 1.84/0.99  --splitting_nvd                         32
% 1.84/0.99  --sub_typing                            true
% 1.84/0.99  --prep_gs_sim                           true
% 1.84/0.99  --prep_unflatten                        true
% 1.84/0.99  --prep_res_sim                          true
% 1.84/0.99  --prep_upred                            true
% 1.84/0.99  --prep_sem_filter                       exhaustive
% 1.84/0.99  --prep_sem_filter_out                   false
% 1.84/0.99  --pred_elim                             true
% 1.84/0.99  --res_sim_input                         true
% 1.84/0.99  --eq_ax_congr_red                       true
% 1.84/0.99  --pure_diseq_elim                       true
% 1.84/0.99  --brand_transform                       false
% 1.84/0.99  --non_eq_to_eq                          false
% 1.84/0.99  --prep_def_merge                        true
% 1.84/0.99  --prep_def_merge_prop_impl              false
% 1.84/0.99  --prep_def_merge_mbd                    true
% 1.84/0.99  --prep_def_merge_tr_red                 false
% 1.84/0.99  --prep_def_merge_tr_cl                  false
% 1.84/0.99  --smt_preprocessing                     true
% 1.84/0.99  --smt_ac_axioms                         fast
% 1.84/0.99  --preprocessed_out                      false
% 1.84/0.99  --preprocessed_stats                    false
% 1.84/0.99  
% 1.84/0.99  ------ Abstraction refinement Options
% 1.84/0.99  
% 1.84/0.99  --abstr_ref                             []
% 1.84/0.99  --abstr_ref_prep                        false
% 1.84/0.99  --abstr_ref_until_sat                   false
% 1.84/0.99  --abstr_ref_sig_restrict                funpre
% 1.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.84/0.99  --abstr_ref_under                       []
% 1.84/0.99  
% 1.84/0.99  ------ SAT Options
% 1.84/0.99  
% 1.84/0.99  --sat_mode                              false
% 1.84/0.99  --sat_fm_restart_options                ""
% 1.84/0.99  --sat_gr_def                            false
% 1.84/0.99  --sat_epr_types                         true
% 1.84/0.99  --sat_non_cyclic_types                  false
% 1.84/0.99  --sat_finite_models                     false
% 1.84/0.99  --sat_fm_lemmas                         false
% 1.84/0.99  --sat_fm_prep                           false
% 1.84/0.99  --sat_fm_uc_incr                        true
% 1.84/0.99  --sat_out_model                         small
% 1.84/0.99  --sat_out_clauses                       false
% 1.84/0.99  
% 1.84/0.99  ------ QBF Options
% 1.84/0.99  
% 1.84/0.99  --qbf_mode                              false
% 1.84/0.99  --qbf_elim_univ                         false
% 1.84/0.99  --qbf_dom_inst                          none
% 1.84/0.99  --qbf_dom_pre_inst                      false
% 1.84/0.99  --qbf_sk_in                             false
% 1.84/0.99  --qbf_pred_elim                         true
% 1.84/0.99  --qbf_split                             512
% 1.84/0.99  
% 1.84/0.99  ------ BMC1 Options
% 1.84/0.99  
% 1.84/0.99  --bmc1_incremental                      false
% 1.84/0.99  --bmc1_axioms                           reachable_all
% 1.84/0.99  --bmc1_min_bound                        0
% 1.84/0.99  --bmc1_max_bound                        -1
% 1.84/0.99  --bmc1_max_bound_default                -1
% 1.84/0.99  --bmc1_symbol_reachability              true
% 1.84/0.99  --bmc1_property_lemmas                  false
% 1.84/0.99  --bmc1_k_induction                      false
% 1.84/0.99  --bmc1_non_equiv_states                 false
% 1.84/0.99  --bmc1_deadlock                         false
% 1.84/0.99  --bmc1_ucm                              false
% 1.84/0.99  --bmc1_add_unsat_core                   none
% 1.84/0.99  --bmc1_unsat_core_children              false
% 1.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.84/0.99  --bmc1_out_stat                         full
% 1.84/0.99  --bmc1_ground_init                      false
% 1.84/0.99  --bmc1_pre_inst_next_state              false
% 1.84/0.99  --bmc1_pre_inst_state                   false
% 1.84/0.99  --bmc1_pre_inst_reach_state             false
% 1.84/0.99  --bmc1_out_unsat_core                   false
% 1.84/0.99  --bmc1_aig_witness_out                  false
% 1.84/0.99  --bmc1_verbose                          false
% 1.84/0.99  --bmc1_dump_clauses_tptp                false
% 1.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.84/0.99  --bmc1_dump_file                        -
% 1.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.84/0.99  --bmc1_ucm_extend_mode                  1
% 1.84/0.99  --bmc1_ucm_init_mode                    2
% 1.84/0.99  --bmc1_ucm_cone_mode                    none
% 1.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.84/0.99  --bmc1_ucm_relax_model                  4
% 1.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.84/0.99  --bmc1_ucm_layered_model                none
% 1.84/0.99  --bmc1_ucm_max_lemma_size               10
% 1.84/0.99  
% 1.84/0.99  ------ AIG Options
% 1.84/0.99  
% 1.84/0.99  --aig_mode                              false
% 1.84/0.99  
% 1.84/0.99  ------ Instantiation Options
% 1.84/0.99  
% 1.84/0.99  --instantiation_flag                    true
% 1.84/0.99  --inst_sos_flag                         false
% 1.84/0.99  --inst_sos_phase                        true
% 1.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.84/0.99  --inst_lit_sel_side                     none
% 1.84/0.99  --inst_solver_per_active                1400
% 1.84/0.99  --inst_solver_calls_frac                1.
% 1.84/0.99  --inst_passive_queue_type               priority_queues
% 1.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.84/0.99  --inst_passive_queues_freq              [25;2]
% 1.84/0.99  --inst_dismatching                      true
% 1.84/0.99  --inst_eager_unprocessed_to_passive     true
% 1.84/0.99  --inst_prop_sim_given                   true
% 1.84/0.99  --inst_prop_sim_new                     false
% 1.84/0.99  --inst_subs_new                         false
% 1.84/0.99  --inst_eq_res_simp                      false
% 1.84/0.99  --inst_subs_given                       false
% 1.84/0.99  --inst_orphan_elimination               true
% 1.84/0.99  --inst_learning_loop_flag               true
% 1.84/0.99  --inst_learning_start                   3000
% 1.84/0.99  --inst_learning_factor                  2
% 1.84/0.99  --inst_start_prop_sim_after_learn       3
% 1.84/0.99  --inst_sel_renew                        solver
% 1.84/0.99  --inst_lit_activity_flag                true
% 1.84/0.99  --inst_restr_to_given                   false
% 1.84/0.99  --inst_activity_threshold               500
% 1.84/0.99  --inst_out_proof                        true
% 1.84/0.99  
% 1.84/0.99  ------ Resolution Options
% 1.84/0.99  
% 1.84/0.99  --resolution_flag                       false
% 1.84/0.99  --res_lit_sel                           adaptive
% 1.84/0.99  --res_lit_sel_side                      none
% 1.84/0.99  --res_ordering                          kbo
% 1.84/0.99  --res_to_prop_solver                    active
% 1.84/0.99  --res_prop_simpl_new                    false
% 1.84/0.99  --res_prop_simpl_given                  true
% 1.84/0.99  --res_passive_queue_type                priority_queues
% 1.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.84/0.99  --res_passive_queues_freq               [15;5]
% 1.84/0.99  --res_forward_subs                      full
% 1.84/0.99  --res_backward_subs                     full
% 1.84/0.99  --res_forward_subs_resolution           true
% 1.84/0.99  --res_backward_subs_resolution          true
% 1.84/0.99  --res_orphan_elimination                true
% 1.84/0.99  --res_time_limit                        2.
% 1.84/0.99  --res_out_proof                         true
% 1.84/0.99  
% 1.84/0.99  ------ Superposition Options
% 1.84/0.99  
% 1.84/0.99  --superposition_flag                    true
% 1.84/0.99  --sup_passive_queue_type                priority_queues
% 1.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.84/0.99  --demod_completeness_check              fast
% 1.84/0.99  --demod_use_ground                      true
% 1.84/0.99  --sup_to_prop_solver                    passive
% 1.84/0.99  --sup_prop_simpl_new                    true
% 1.84/0.99  --sup_prop_simpl_given                  true
% 1.84/0.99  --sup_fun_splitting                     false
% 1.84/0.99  --sup_smt_interval                      50000
% 1.84/0.99  
% 1.84/0.99  ------ Superposition Simplification Setup
% 1.84/0.99  
% 1.84/0.99  --sup_indices_passive                   []
% 1.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_full_bw                           [BwDemod]
% 1.84/0.99  --sup_immed_triv                        [TrivRules]
% 1.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_immed_bw_main                     []
% 1.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.84/0.99  
% 1.84/0.99  ------ Combination Options
% 1.84/0.99  
% 1.84/0.99  --comb_res_mult                         3
% 1.84/0.99  --comb_sup_mult                         2
% 1.84/0.99  --comb_inst_mult                        10
% 1.84/0.99  
% 1.84/0.99  ------ Debug Options
% 1.84/0.99  
% 1.84/0.99  --dbg_backtrace                         false
% 1.84/0.99  --dbg_dump_prop_clauses                 false
% 1.84/0.99  --dbg_dump_prop_clauses_file            -
% 1.84/0.99  --dbg_out_stat                          false
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  ------ Proving...
% 1.84/0.99  
% 1.84/0.99  
% 1.84/0.99  % SZS status Theorem for theBenchmark.p
% 1.84/0.99  
% 1.84/0.99   Resolution empty clause
% 1.84/0.99  
% 1.84/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.84/0.99  
% 1.84/0.99  fof(f2,axiom,(
% 1.84/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f36,plain,(
% 1.84/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.84/0.99    inference(nnf_transformation,[],[f2])).
% 1.84/0.99  
% 1.84/0.99  fof(f48,plain,(
% 1.84/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f36])).
% 1.84/0.99  
% 1.84/0.99  fof(f12,conjecture,(
% 1.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f13,negated_conjecture,(
% 1.84/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.84/0.99    inference(negated_conjecture,[],[f12])).
% 1.84/0.99  
% 1.84/0.99  fof(f32,plain,(
% 1.84/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.84/0.99    inference(ennf_transformation,[],[f13])).
% 1.84/0.99  
% 1.84/0.99  fof(f33,plain,(
% 1.84/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.84/0.99    inference(flattening,[],[f32])).
% 1.84/0.99  
% 1.84/0.99  fof(f38,plain,(
% 1.84/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.84/0.99    inference(nnf_transformation,[],[f33])).
% 1.84/0.99  
% 1.84/0.99  fof(f39,plain,(
% 1.84/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.84/0.99    inference(flattening,[],[f38])).
% 1.84/0.99  
% 1.84/0.99  fof(f42,plain,(
% 1.84/0.99    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & (r1_waybel_7(X0,X1,sK2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.84/0.99    introduced(choice_axiom,[])).
% 1.84/0.99  
% 1.84/0.99  fof(f41,plain,(
% 1.84/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & (r1_waybel_7(X0,sK1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK1))) )),
% 1.84/0.99    introduced(choice_axiom,[])).
% 1.84/0.99  
% 1.84/0.99  fof(f40,plain,(
% 1.84/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.84/0.99    introduced(choice_axiom,[])).
% 1.84/0.99  
% 1.84/0.99  fof(f43,plain,(
% 1.84/0.99    (((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f42,f41,f40])).
% 1.84/0.99  
% 1.84/0.99  fof(f67,plain,(
% 1.84/0.99    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.84/0.99    inference(cnf_transformation,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f6,axiom,(
% 1.84/0.99    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f52,plain,(
% 1.84/0.99    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.84/0.99    inference(cnf_transformation,[],[f6])).
% 1.84/0.99  
% 1.84/0.99  fof(f82,plain,(
% 1.84/0.99    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.84/0.99    inference(definition_unfolding,[],[f67,f52])).
% 1.84/0.99  
% 1.84/0.99  fof(f7,axiom,(
% 1.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f16,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.84/0.99    inference(pure_predicate_removal,[],[f7])).
% 1.84/0.99  
% 1.84/0.99  fof(f22,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.84/0.99    inference(ennf_transformation,[],[f16])).
% 1.84/0.99  
% 1.84/0.99  fof(f23,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.84/0.99    inference(flattening,[],[f22])).
% 1.84/0.99  
% 1.84/0.99  fof(f54,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f23])).
% 1.84/0.99  
% 1.84/0.99  fof(f73,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(definition_unfolding,[],[f54,f52,f52,f52])).
% 1.84/0.99  
% 1.84/0.99  fof(f72,plain,(
% 1.84/0.99    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.84/0.99    inference(cnf_transformation,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f10,axiom,(
% 1.84/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f28,plain,(
% 1.84/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.84/0.99    inference(ennf_transformation,[],[f10])).
% 1.84/0.99  
% 1.84/0.99  fof(f29,plain,(
% 1.84/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.84/0.99    inference(flattening,[],[f28])).
% 1.84/0.99  
% 1.84/0.99  fof(f37,plain,(
% 1.84/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.84/0.99    inference(nnf_transformation,[],[f29])).
% 1.84/0.99  
% 1.84/0.99  fof(f60,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f37])).
% 1.84/0.99  
% 1.84/0.99  fof(f63,plain,(
% 1.84/0.99    v2_pre_topc(sK0)),
% 1.84/0.99    inference(cnf_transformation,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f62,plain,(
% 1.84/0.99    ~v2_struct_0(sK0)),
% 1.84/0.99    inference(cnf_transformation,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f64,plain,(
% 1.84/0.99    l1_pre_topc(sK0)),
% 1.84/0.99    inference(cnf_transformation,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f70,plain,(
% 1.84/0.99    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.84/0.99    inference(cnf_transformation,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f4,axiom,(
% 1.84/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f19,plain,(
% 1.84/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.84/0.99    inference(ennf_transformation,[],[f4])).
% 1.84/0.99  
% 1.84/0.99  fof(f50,plain,(
% 1.84/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f19])).
% 1.84/0.99  
% 1.84/0.99  fof(f68,plain,(
% 1.84/0.99    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.84/0.99    inference(cnf_transformation,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f81,plain,(
% 1.84/0.99    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.84/0.99    inference(definition_unfolding,[],[f68,f52])).
% 1.84/0.99  
% 1.84/0.99  fof(f65,plain,(
% 1.84/0.99    ~v1_xboole_0(sK1)),
% 1.84/0.99    inference(cnf_transformation,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f5,axiom,(
% 1.84/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f20,plain,(
% 1.84/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.84/0.99    inference(ennf_transformation,[],[f5])).
% 1.84/0.99  
% 1.84/0.99  fof(f21,plain,(
% 1.84/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.84/0.99    inference(flattening,[],[f20])).
% 1.84/0.99  
% 1.84/0.99  fof(f51,plain,(
% 1.84/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f21])).
% 1.84/0.99  
% 1.84/0.99  fof(f8,axiom,(
% 1.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f14,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.84/0.99    inference(pure_predicate_removal,[],[f8])).
% 1.84/0.99  
% 1.84/0.99  fof(f15,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.84/0.99    inference(pure_predicate_removal,[],[f14])).
% 1.84/0.99  
% 1.84/0.99  fof(f24,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.84/0.99    inference(ennf_transformation,[],[f15])).
% 1.84/0.99  
% 1.84/0.99  fof(f25,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.84/0.99    inference(flattening,[],[f24])).
% 1.84/0.99  
% 1.84/0.99  fof(f56,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f25])).
% 1.84/0.99  
% 1.84/0.99  fof(f75,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(definition_unfolding,[],[f56,f52,f52,f52])).
% 1.84/0.99  
% 1.84/0.99  fof(f9,axiom,(
% 1.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f17,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.84/0.99    inference(pure_predicate_removal,[],[f9])).
% 1.84/0.99  
% 1.84/0.99  fof(f26,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.84/0.99    inference(ennf_transformation,[],[f17])).
% 1.84/0.99  
% 1.84/0.99  fof(f27,plain,(
% 1.84/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.84/0.99    inference(flattening,[],[f26])).
% 1.84/0.99  
% 1.84/0.99  fof(f58,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f27])).
% 1.84/0.99  
% 1.84/0.99  fof(f77,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(definition_unfolding,[],[f58,f52,f52,f52,f52])).
% 1.84/0.99  
% 1.84/0.99  fof(f66,plain,(
% 1.84/0.99    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.84/0.99    inference(cnf_transformation,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f83,plain,(
% 1.84/0.99    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.84/0.99    inference(definition_unfolding,[],[f66,f52])).
% 1.84/0.99  
% 1.84/0.99  fof(f53,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f23])).
% 1.84/0.99  
% 1.84/0.99  fof(f74,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(definition_unfolding,[],[f53,f52,f52,f52])).
% 1.84/0.99  
% 1.84/0.99  fof(f3,axiom,(
% 1.84/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f18,plain,(
% 1.84/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.84/0.99    inference(ennf_transformation,[],[f3])).
% 1.84/0.99  
% 1.84/0.99  fof(f49,plain,(
% 1.84/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f18])).
% 1.84/0.99  
% 1.84/0.99  fof(f11,axiom,(
% 1.84/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f30,plain,(
% 1.84/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.84/0.99    inference(ennf_transformation,[],[f11])).
% 1.84/0.99  
% 1.84/0.99  fof(f31,plain,(
% 1.84/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.84/0.99    inference(flattening,[],[f30])).
% 1.84/0.99  
% 1.84/0.99  fof(f61,plain,(
% 1.84/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f31])).
% 1.84/0.99  
% 1.84/0.99  fof(f79,plain,(
% 1.84/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(definition_unfolding,[],[f61,f52,f52,f52,f52])).
% 1.84/0.99  
% 1.84/0.99  fof(f69,plain,(
% 1.84/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.84/0.99    inference(cnf_transformation,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f80,plain,(
% 1.84/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.84/0.99    inference(definition_unfolding,[],[f69,f52])).
% 1.84/0.99  
% 1.84/0.99  fof(f71,plain,(
% 1.84/0.99    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.84/0.99    inference(cnf_transformation,[],[f43])).
% 1.84/0.99  
% 1.84/0.99  fof(f59,plain,(
% 1.84/0.99    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.84/0.99    inference(cnf_transformation,[],[f37])).
% 1.84/0.99  
% 1.84/0.99  fof(f1,axiom,(
% 1.84/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.84/0.99  
% 1.84/0.99  fof(f34,plain,(
% 1.84/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.99    inference(nnf_transformation,[],[f1])).
% 1.84/0.99  
% 1.84/0.99  fof(f35,plain,(
% 1.84/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.84/0.99    inference(flattening,[],[f34])).
% 1.84/0.99  
% 1.84/0.99  fof(f44,plain,(
% 1.84/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.84/0.99    inference(cnf_transformation,[],[f35])).
% 1.84/0.99  
% 1.84/0.99  fof(f85,plain,(
% 1.84/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.84/0.99    inference(equality_resolution,[],[f44])).
% 1.84/0.99  
% 1.84/0.99  cnf(c_3,plain,
% 1.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.84/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_3881,plain,
% 1.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 1.84/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 1.84/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_22,negated_conjecture,
% 1.84/0.99      ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.84/0.99      inference(cnf_transformation,[],[f82]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_8,plain,
% 1.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | v2_struct_0(X2)
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | ~ l1_struct_0(X2) ),
% 1.84/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_17,negated_conjecture,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.84/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_209,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.84/0.99      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_14,plain,
% 1.84/0.99      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.84/0.99      | r3_waybel_9(X0,X1,X2)
% 1.84/0.99      | ~ l1_waybel_0(X1,X0)
% 1.84/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.84/0.99      | ~ v2_pre_topc(X0)
% 1.84/0.99      | ~ v7_waybel_0(X1)
% 1.84/0.99      | ~ v4_orders_2(X1)
% 1.84/0.99      | v2_struct_0(X0)
% 1.84/0.99      | v2_struct_0(X1)
% 1.84/0.99      | ~ l1_pre_topc(X0) ),
% 1.84/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_26,negated_conjecture,
% 1.84/0.99      ( v2_pre_topc(sK0) ),
% 1.84/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_493,plain,
% 1.84/0.99      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.84/0.99      | r3_waybel_9(X0,X1,X2)
% 1.84/0.99      | ~ l1_waybel_0(X1,X0)
% 1.84/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.84/0.99      | ~ v7_waybel_0(X1)
% 1.84/0.99      | ~ v4_orders_2(X1)
% 1.84/0.99      | v2_struct_0(X0)
% 1.84/0.99      | v2_struct_0(X1)
% 1.84/0.99      | ~ l1_pre_topc(X0)
% 1.84/0.99      | sK0 != X0 ),
% 1.84/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_494,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.84/0.99      | r3_waybel_9(sK0,X0,X1)
% 1.84/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.84/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.84/0.99      | ~ v7_waybel_0(X0)
% 1.84/0.99      | ~ v4_orders_2(X0)
% 1.84/0.99      | v2_struct_0(X0)
% 1.84/0.99      | v2_struct_0(sK0)
% 1.84/0.99      | ~ l1_pre_topc(sK0) ),
% 1.84/0.99      inference(unflattening,[status(thm)],[c_493]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_27,negated_conjecture,
% 1.84/0.99      ( ~ v2_struct_0(sK0) ),
% 1.84/0.99      inference(cnf_transformation,[],[f62]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_25,negated_conjecture,
% 1.84/0.99      ( l1_pre_topc(sK0) ),
% 1.84/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_498,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.84/0.99      | r3_waybel_9(sK0,X0,X1)
% 1.84/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.84/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.84/0.99      | ~ v7_waybel_0(X0)
% 1.84/0.99      | ~ v4_orders_2(X0)
% 1.84/0.99      | v2_struct_0(X0) ),
% 1.84/0.99      inference(global_propositional_subsumption,
% 1.84/0.99                [status(thm)],
% 1.84/0.99                [c_494,c_27,c_25]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_871,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.84/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.84/0.99      | ~ v7_waybel_0(X0)
% 1.84/0.99      | ~ v4_orders_2(X0)
% 1.84/0.99      | v2_struct_0(X0)
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 1.84/0.99      | sK2 != X1
% 1.84/0.99      | sK0 != sK0 ),
% 1.84/0.99      inference(resolution_lifted,[status(thm)],[c_209,c_498]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_872,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.84/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.84/0.99      inference(unflattening,[status(thm)],[c_871]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_19,negated_conjecture,
% 1.84/0.99      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 1.84/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_874,plain,
% 1.84/0.99      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.84/0.99      inference(global_propositional_subsumption,[status(thm)],[c_872,c_19]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_875,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.84/0.99      inference(renaming,[status(thm)],[c_874]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_911,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(X2)
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | ~ l1_struct_0(X2)
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 1.84/0.99      | sK0 != X2 ),
% 1.84/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_875]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_912,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(sK0)
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | ~ l1_struct_0(sK0)
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.84/0.99      inference(unflattening,[status(thm)],[c_911]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_6,plain,
% 1.84/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.84/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_68,plain,
% 1.84/0.99      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_916,plain,
% 1.84/0.99      ( v1_xboole_0(X0)
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.84/0.99      inference(global_propositional_subsumption,
% 1.84/0.99                [status(thm)],
% 1.84/0.99                [c_912,c_27,c_25,c_68]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_917,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.84/0.99      inference(renaming,[status(thm)],[c_916]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_21,negated_conjecture,
% 1.84/0.99      ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.84/0.99      inference(cnf_transformation,[],[f81]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1505,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 1.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.84/0.99      | sK1 != X0 ),
% 1.84/0.99      inference(resolution_lifted,[status(thm)],[c_917,c_21]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1506,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | v1_xboole_0(sK1)
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/0.99      inference(unflattening,[status(thm)],[c_1505]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_24,negated_conjecture,
% 1.84/0.99      ( ~ v1_xboole_0(sK1) ),
% 1.84/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1510,plain,
% 1.84/0.99      ( v1_xboole_0(X0)
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1506,c_24]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1511,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/0.99      inference(renaming,[status(thm)],[c_1510]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1854,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.84/0.99      | sK1 != sK1 ),
% 1.84/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_1511]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_7,plain,
% 1.84/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 1.84/0.99      inference(cnf_transformation,[],[f51]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_542,plain,
% 1.84/0.99      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.84/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_543,plain,
% 1.84/0.99      ( l1_struct_0(sK0) ),
% 1.84/0.99      inference(unflattening,[status(thm)],[c_542]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1020,plain,
% 1.84/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK0 != X0 ),
% 1.84/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_543]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1021,plain,
% 1.84/0.99      ( v2_struct_0(sK0) | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.84/0.99      inference(unflattening,[status(thm)],[c_1020]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_65,plain,
% 1.84/0.99      ( v2_struct_0(sK0)
% 1.84/0.99      | ~ v1_xboole_0(u1_struct_0(sK0))
% 1.84/0.99      | ~ l1_struct_0(sK0) ),
% 1.84/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1023,plain,
% 1.84/0.99      ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.84/0.99      inference(global_propositional_subsumption,
% 1.84/0.99                [status(thm)],
% 1.84/0.99                [c_1021,c_27,c_25,c_65,c_68]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_2558,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.84/0.99      | u1_struct_0(sK0) != X0
% 1.84/0.99      | sK1 != sK1 ),
% 1.84/0.99      inference(resolution_lifted,[status(thm)],[c_1854,c_1023]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_2559,plain,
% 1.84/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.84/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
% 1.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.84/0.99      inference(unflattening,[status(thm)],[c_2558]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_10,plain,
% 1.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.84/0.99      | v2_struct_0(X2)
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | ~ l1_struct_0(X2) ),
% 1.84/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1036,plain,
% 1.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.84/0.99      | v2_struct_0(X2)
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | sK0 != X2 ),
% 1.84/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_543]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1037,plain,
% 1.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.84/0.99      | v2_struct_0(sK0)
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | v1_xboole_0(X0) ),
% 1.84/0.99      inference(unflattening,[status(thm)],[c_1036]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1041,plain,
% 1.84/0.99      ( v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | v1_xboole_0(X0) ),
% 1.84/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1037,c_27]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1042,plain,
% 1.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | v1_xboole_0(X0) ),
% 1.84/0.99      inference(renaming,[status(thm)],[c_1041]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1430,plain,
% 1.84/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.84/0.99      | v1_xboole_0(X1)
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.84/0.99      | sK1 != X0 ),
% 1.84/0.99      inference(resolution_lifted,[status(thm)],[c_1042,c_21]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1431,plain,
% 1.84/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | v1_xboole_0(sK1)
% 1.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/0.99      inference(unflattening,[status(thm)],[c_1430]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1435,plain,
% 1.84/0.99      ( v1_xboole_0(X0)
% 1.84/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.84/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1431,c_24]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1436,plain,
% 1.84/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.84/0.99      | v1_xboole_0(X0)
% 1.84/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/0.99      inference(renaming,[status(thm)],[c_1435]) ).
% 1.84/0.99  
% 1.84/0.99  cnf(c_1930,plain,
% 1.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.84/1.00      | sK1 != sK1 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_1436]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_2511,plain,
% 1.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.84/1.00      | u1_struct_0(sK0) != X0
% 1.84/1.00      | sK1 != sK1 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_1930,c_1023]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_2512,plain,
% 1.84/1.00      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.84/1.00      | v4_orders_2(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_2511]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_2812,plain,
% 1.84/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_2559,c_2512]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_12,plain,
% 1.84/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.84/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.84/1.00      | v2_struct_0(X2)
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | ~ l1_struct_0(X2) ),
% 1.84/1.00      inference(cnf_transformation,[],[f77]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_23,negated_conjecture,
% 1.84/1.00      ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
% 1.84/1.00      inference(cnf_transformation,[],[f83]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_370,plain,
% 1.84/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.84/1.00      | v2_struct_0(X2)
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | ~ l1_struct_0(X2)
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | sK1 != X0 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_371,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.84/1.00      | v2_struct_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | v1_xboole_0(sK1)
% 1.84/1.00      | ~ l1_struct_0(X1)
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_370]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_375,plain,
% 1.84/1.00      ( v1_xboole_0(X0)
% 1.84/1.00      | v2_struct_0(X1)
% 1.84/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ l1_struct_0(X1)
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_371,c_24]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_376,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.84/1.00      | v2_struct_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | ~ l1_struct_0(X1)
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.84/1.00      inference(renaming,[status(thm)],[c_375]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1102,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.84/1.00      | v2_struct_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | sK0 != X1 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_376,c_543]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1103,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | v2_struct_0(sK0)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_1102]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1107,plain,
% 1.84/1.00      ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1103,c_27]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1108,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.84/1.00      inference(renaming,[status(thm)],[c_1107]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1550,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | sK1 != sK1 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_1108]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1828,plain,
% 1.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | sK1 != sK1 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_1550]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_2589,plain,
% 1.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | u1_struct_0(sK0) != X0
% 1.84/1.00      | sK1 != sK1 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_1828,c_1023]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_2590,plain,
% 1.84/1.00      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.84/1.00      | v7_waybel_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_2589]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3073,plain,
% 1.84/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_2812,c_2590]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_9,plain,
% 1.84/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | v2_struct_0(X2)
% 1.84/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | ~ l1_struct_0(X2) ),
% 1.84/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1069,plain,
% 1.84/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | v2_struct_0(X2)
% 1.84/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | sK0 != X2 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_543]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1070,plain,
% 1.84/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.84/1.00      | v2_struct_0(sK0)
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_1069]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1074,plain,
% 1.84/1.00      ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0) ),
% 1.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1070,c_27]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1075,plain,
% 1.84/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0) ),
% 1.84/1.00      inference(renaming,[status(thm)],[c_1074]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1400,plain,
% 1.84/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.84/1.00      | sK1 != X0 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_1075,c_21]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1401,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | v1_xboole_0(sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_1400]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1405,plain,
% 1.84/1.00      ( v1_xboole_0(X0)
% 1.84/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1401,c_24]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1406,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/1.00      inference(renaming,[status(thm)],[c_1405]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1953,plain,
% 1.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.84/1.00      | sK1 != sK1 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_1406]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_2495,plain,
% 1.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.84/1.00      | u1_struct_0(sK0) != X0
% 1.84/1.00      | sK1 != sK1 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_1953,c_1023]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_2496,plain,
% 1.84/1.00      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.84/1.00      | ~ v2_struct_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_2495]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3376,plain,
% 1.84/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.84/1.00      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_3073,c_2496]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3875,plain,
% 1.84/1.00      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.84/1.00      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.84/1.00      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.84/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 1.84/1.00      inference(predicate_to_equality,[status(thm)],[c_3376]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_5,plain,
% 1.84/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.84/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1031,plain,
% 1.84/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_543]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1032,plain,
% 1.84/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_1031]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_16,plain,
% 1.84/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.84/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.84/1.00      | v2_struct_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | ~ l1_struct_0(X1)
% 1.84/1.00      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 1.84/1.00      inference(cnf_transformation,[],[f79]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_409,plain,
% 1.84/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.84/1.00      | v2_struct_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | ~ l1_struct_0(X1)
% 1.84/1.00      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.84/1.00      | sK1 != X0 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_410,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.84/1.00      | v2_struct_0(X0)
% 1.84/1.00      | v1_xboole_0(sK1)
% 1.84/1.00      | ~ l1_struct_0(X0)
% 1.84/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_409]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_414,plain,
% 1.84/1.00      ( v2_struct_0(X0)
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.84/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.84/1.00      | ~ l1_struct_0(X0)
% 1.84/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_410,c_24]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_415,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.84/1.00      | v2_struct_0(X0)
% 1.84/1.00      | ~ l1_struct_0(X0)
% 1.84/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.84/1.00      inference(renaming,[status(thm)],[c_414]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1009,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.84/1.00      | v2_struct_0(X0)
% 1.84/1.00      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.84/1.00      | sK0 != X0 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_415,c_543]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1010,plain,
% 1.84/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.84/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.84/1.00      | v2_struct_0(sK0)
% 1.84/1.00      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_1009]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_20,negated_conjecture,
% 1.84/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
% 1.84/1.00      inference(cnf_transformation,[],[f80]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1012,plain,
% 1.84/1.00      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.84/1.00      inference(global_propositional_subsumption,
% 1.84/1.00                [status(thm)],
% 1.84/1.00                [c_1010,c_27,c_22,c_21,c_20]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3482,plain,
% 1.84/1.00      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.84/1.00      inference(equality_resolution_simp,[status(thm)],[c_1012]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3943,plain,
% 1.84/1.00      ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.84/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.84/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.84/1.00      inference(light_normalisation,[status(thm)],[c_3875,c_1032,c_3482]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3944,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.84/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.84/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.84/1.00      inference(equality_resolution_simp,[status(thm)],[c_3943]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3878,plain,
% 1.84/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
% 1.84/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_18,negated_conjecture,
% 1.84/1.00      ( r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.84/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_211,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.84/1.00      inference(prop_impl,[status(thm)],[c_18]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_15,plain,
% 1.84/1.00      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.84/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 1.84/1.00      | ~ l1_waybel_0(X1,X0)
% 1.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.84/1.00      | ~ v2_pre_topc(X0)
% 1.84/1.00      | ~ v7_waybel_0(X1)
% 1.84/1.00      | ~ v4_orders_2(X1)
% 1.84/1.00      | v2_struct_0(X0)
% 1.84/1.00      | v2_struct_0(X1)
% 1.84/1.00      | ~ l1_pre_topc(X0) ),
% 1.84/1.00      inference(cnf_transformation,[],[f59]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_460,plain,
% 1.84/1.00      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.84/1.00      | ~ r3_waybel_9(X0,X1,X2)
% 1.84/1.00      | ~ l1_waybel_0(X1,X0)
% 1.84/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.84/1.00      | ~ v7_waybel_0(X1)
% 1.84/1.00      | ~ v4_orders_2(X1)
% 1.84/1.00      | v2_struct_0(X0)
% 1.84/1.00      | v2_struct_0(X1)
% 1.84/1.00      | ~ l1_pre_topc(X0)
% 1.84/1.00      | sK0 != X0 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_461,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.84/1.00      | ~ r3_waybel_9(sK0,X0,X1)
% 1.84/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.84/1.00      | ~ v7_waybel_0(X0)
% 1.84/1.00      | ~ v4_orders_2(X0)
% 1.84/1.00      | v2_struct_0(X0)
% 1.84/1.00      | v2_struct_0(sK0)
% 1.84/1.00      | ~ l1_pre_topc(sK0) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_460]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_465,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.84/1.00      | ~ r3_waybel_9(sK0,X0,X1)
% 1.84/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.84/1.00      | ~ v7_waybel_0(X0)
% 1.84/1.00      | ~ v4_orders_2(X0)
% 1.84/1.00      | v2_struct_0(X0) ),
% 1.84/1.00      inference(global_propositional_subsumption,
% 1.84/1.00                [status(thm)],
% 1.84/1.00                [c_461,c_27,c_25]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_845,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ l1_waybel_0(X0,sK0)
% 1.84/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.84/1.00      | ~ v7_waybel_0(X0)
% 1.84/1.00      | ~ v4_orders_2(X0)
% 1.84/1.00      | v2_struct_0(X0)
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 1.84/1.00      | sK2 != X1
% 1.84/1.00      | sK0 != sK0 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_211,c_465]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_846,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.84/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_845]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_848,plain,
% 1.84/1.00      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_846,c_19]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_849,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.84/1.00      inference(renaming,[status(thm)],[c_848]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_959,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(X2)
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | ~ l1_struct_0(X2)
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 1.84/1.00      | sK0 != X2 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_849]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_960,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(sK0)
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | ~ l1_struct_0(sK0)
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_959]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_964,plain,
% 1.84/1.00      ( v1_xboole_0(X0)
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.84/1.00      inference(global_propositional_subsumption,
% 1.84/1.00                [status(thm)],
% 1.84/1.00                [c_960,c_27,c_25,c_68]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_965,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.84/1.00      inference(renaming,[status(thm)],[c_964]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1460,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.84/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v1_xboole_0(X1)
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.84/1.00      | sK1 != X0 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_965,c_21]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1461,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | v1_xboole_0(sK1)
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_1460]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1465,plain,
% 1.84/1.00      ( v1_xboole_0(X0)
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1461,c_24]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1466,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.84/1.00      inference(renaming,[status(thm)],[c_1465]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_1892,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v1_xboole_0(X0)
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.84/1.00      | sK1 != sK1 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_1466]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_2527,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.84/1.00      | u1_struct_0(sK0) != X0
% 1.84/1.00      | sK1 != sK1 ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_1892,c_1023]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_2528,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.84/1.00      inference(unflattening,[status(thm)],[c_2527]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_2839,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.84/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_2528,c_2512]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3046,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.84/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.84/1.00      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_2839,c_2590]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3400,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2)
% 1.84/1.00      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.84/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.84/1.00      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.84/1.00      inference(resolution_lifted,[status(thm)],[c_3046,c_2496]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3874,plain,
% 1.84/1.00      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.84/1.00      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.84/1.00      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.84/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 1.84/1.00      inference(predicate_to_equality,[status(thm)],[c_3400]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3935,plain,
% 1.84/1.00      ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.84/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.84/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.84/1.00      | r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.84/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.84/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.84/1.00      inference(light_normalisation,[status(thm)],[c_3874,c_1032,c_3482]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3936,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.84/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.84/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.84/1.00      inference(equality_resolution_simp,[status(thm)],[c_3935]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3940,plain,
% 1.84/1.00      ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.84/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.84/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3936,c_3878]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3948,plain,
% 1.84/1.00      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.84/1.00      inference(forward_subsumption_resolution,
% 1.84/1.00                [status(thm)],
% 1.84/1.00                [c_3944,c_3878,c_3940]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_4171,plain,
% 1.84/1.00      ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
% 1.84/1.00      inference(superposition,[status(thm)],[c_3881,c_3948]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f85]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_3882,plain,
% 1.84/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 1.84/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.84/1.00  
% 1.84/1.00  cnf(c_4265,plain,
% 1.84/1.00      ( $false ),
% 1.84/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4171,c_3882]) ).
% 1.84/1.00  
% 1.84/1.00  
% 1.84/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.84/1.00  
% 1.84/1.00  ------                               Statistics
% 1.84/1.00  
% 1.84/1.00  ------ General
% 1.84/1.00  
% 1.84/1.00  abstr_ref_over_cycles:                  0
% 1.84/1.00  abstr_ref_under_cycles:                 0
% 1.84/1.00  gc_basic_clause_elim:                   0
% 1.84/1.00  forced_gc_time:                         0
% 1.84/1.00  parsing_time:                           0.01
% 1.84/1.00  unif_index_cands_time:                  0.
% 1.84/1.00  unif_index_add_time:                    0.
% 1.84/1.00  orderings_time:                         0.
% 1.84/1.00  out_proof_time:                         0.014
% 1.84/1.00  total_time:                             0.159
% 1.84/1.00  num_of_symbols:                         56
% 1.84/1.00  num_of_terms:                           1532
% 1.84/1.00  
% 1.84/1.00  ------ Preprocessing
% 1.84/1.00  
% 1.84/1.00  num_of_splits:                          0
% 1.84/1.00  num_of_split_atoms:                     0
% 1.84/1.00  num_of_reused_defs:                     0
% 1.84/1.00  num_eq_ax_congr_red:                    9
% 1.84/1.00  num_of_sem_filtered_clauses:            1
% 1.84/1.00  num_of_subtypes:                        0
% 1.84/1.00  monotx_restored_types:                  0
% 1.84/1.00  sat_num_of_epr_types:                   0
% 1.84/1.00  sat_num_of_non_cyclic_types:            0
% 1.84/1.00  sat_guarded_non_collapsed_types:        0
% 1.84/1.00  num_pure_diseq_elim:                    0
% 1.84/1.00  simp_replaced_by:                       0
% 1.84/1.00  res_preprocessed:                       84
% 1.84/1.00  prep_upred:                             0
% 1.84/1.00  prep_unflattend:                        39
% 1.84/1.00  smt_new_axioms:                         0
% 1.84/1.00  pred_elim_cands:                        3
% 1.84/1.00  pred_elim:                              12
% 1.84/1.00  pred_elim_cl:                           13
% 1.84/1.00  pred_elim_cycles:                       24
% 1.84/1.00  merged_defs:                            10
% 1.84/1.00  merged_defs_ncl:                        0
% 1.84/1.00  bin_hyper_res:                          10
% 1.84/1.00  prep_cycles:                            4
% 1.84/1.00  pred_elim_time:                         0.09
% 1.84/1.00  splitting_time:                         0.
% 1.84/1.00  sem_filter_time:                        0.
% 1.84/1.00  monotx_time:                            0.
% 1.84/1.00  subtype_inf_time:                       0.
% 1.84/1.00  
% 1.84/1.00  ------ Problem properties
% 1.84/1.00  
% 1.84/1.00  clauses:                                12
% 1.84/1.00  conjectures:                            2
% 1.84/1.00  epr:                                    2
% 1.84/1.00  horn:                                   10
% 1.84/1.00  ground:                                 8
% 1.84/1.00  unary:                                  5
% 1.84/1.00  binary:                                 2
% 1.84/1.00  lits:                                   40
% 1.84/1.00  lits_eq:                                15
% 1.84/1.00  fd_pure:                                0
% 1.84/1.00  fd_pseudo:                              0
% 1.84/1.00  fd_cond:                                0
% 1.84/1.00  fd_pseudo_cond:                         1
% 1.84/1.00  ac_symbols:                             0
% 1.84/1.00  
% 1.84/1.00  ------ Propositional Solver
% 1.84/1.00  
% 1.84/1.00  prop_solver_calls:                      25
% 1.84/1.00  prop_fast_solver_calls:                 1653
% 1.84/1.00  smt_solver_calls:                       0
% 1.84/1.00  smt_fast_solver_calls:                  0
% 1.84/1.00  prop_num_of_clauses:                    596
% 1.84/1.00  prop_preprocess_simplified:             2415
% 1.84/1.00  prop_fo_subsumed:                       53
% 1.84/1.00  prop_solver_time:                       0.
% 1.84/1.00  smt_solver_time:                        0.
% 1.84/1.00  smt_fast_solver_time:                   0.
% 1.84/1.00  prop_fast_solver_time:                  0.
% 1.84/1.00  prop_unsat_core_time:                   0.
% 1.84/1.00  
% 1.84/1.00  ------ QBF
% 1.84/1.00  
% 1.84/1.00  qbf_q_res:                              0
% 1.84/1.00  qbf_num_tautologies:                    0
% 1.84/1.00  qbf_prep_cycles:                        0
% 1.84/1.00  
% 1.84/1.00  ------ BMC1
% 1.84/1.00  
% 1.84/1.00  bmc1_current_bound:                     -1
% 1.84/1.00  bmc1_last_solved_bound:                 -1
% 1.84/1.00  bmc1_unsat_core_size:                   -1
% 1.84/1.00  bmc1_unsat_core_parents_size:           -1
% 1.84/1.00  bmc1_merge_next_fun:                    0
% 1.84/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.84/1.00  
% 1.84/1.00  ------ Instantiation
% 1.84/1.00  
% 1.84/1.00  inst_num_of_clauses:                    80
% 1.84/1.00  inst_num_in_passive:                    21
% 1.84/1.00  inst_num_in_active:                     54
% 1.84/1.00  inst_num_in_unprocessed:                5
% 1.84/1.00  inst_num_of_loops:                      60
% 1.84/1.00  inst_num_of_learning_restarts:          0
% 1.84/1.00  inst_num_moves_active_passive:          3
% 1.84/1.00  inst_lit_activity:                      0
% 1.84/1.00  inst_lit_activity_moves:                0
% 1.84/1.00  inst_num_tautologies:                   0
% 1.84/1.00  inst_num_prop_implied:                  0
% 1.84/1.00  inst_num_existing_simplified:           0
% 1.84/1.00  inst_num_eq_res_simplified:             0
% 1.84/1.00  inst_num_child_elim:                    0
% 1.84/1.00  inst_num_of_dismatching_blockings:      5
% 1.84/1.00  inst_num_of_non_proper_insts:           67
% 1.84/1.00  inst_num_of_duplicates:                 0
% 1.84/1.00  inst_inst_num_from_inst_to_res:         0
% 1.84/1.00  inst_dismatching_checking_time:         0.
% 1.84/1.00  
% 1.84/1.00  ------ Resolution
% 1.84/1.00  
% 1.84/1.00  res_num_of_clauses:                     0
% 1.84/1.00  res_num_in_passive:                     0
% 1.84/1.00  res_num_in_active:                      0
% 1.84/1.00  res_num_of_loops:                       88
% 1.84/1.00  res_forward_subset_subsumed:            7
% 1.84/1.00  res_backward_subset_subsumed:           0
% 1.84/1.00  res_forward_subsumed:                   6
% 1.84/1.00  res_backward_subsumed:                  10
% 1.84/1.00  res_forward_subsumption_resolution:     2
% 1.84/1.00  res_backward_subsumption_resolution:    0
% 1.84/1.00  res_clause_to_clause_subsumption:       266
% 1.84/1.00  res_orphan_elimination:                 0
% 1.84/1.00  res_tautology_del:                      26
% 1.84/1.00  res_num_eq_res_simplified:              1
% 1.84/1.00  res_num_sel_changes:                    0
% 1.84/1.00  res_moves_from_active_to_pass:          0
% 1.84/1.00  
% 1.84/1.00  ------ Superposition
% 1.84/1.00  
% 1.84/1.00  sup_time_total:                         0.
% 1.84/1.00  sup_time_generating:                    0.
% 1.84/1.00  sup_time_sim_full:                      0.
% 1.84/1.00  sup_time_sim_immed:                     0.
% 1.84/1.00  
% 1.84/1.00  sup_num_of_clauses:                     13
% 1.84/1.00  sup_num_in_active:                      10
% 1.84/1.00  sup_num_in_passive:                     3
% 1.84/1.00  sup_num_of_loops:                       10
% 1.84/1.00  sup_fw_superposition:                   2
% 1.84/1.00  sup_bw_superposition:                   2
% 1.84/1.00  sup_immediate_simplified:               0
% 1.84/1.00  sup_given_eliminated:                   0
% 1.84/1.00  comparisons_done:                       0
% 1.84/1.00  comparisons_avoided:                    0
% 1.84/1.00  
% 1.84/1.00  ------ Simplifications
% 1.84/1.00  
% 1.84/1.00  
% 1.84/1.00  sim_fw_subset_subsumed:                 0
% 1.84/1.00  sim_bw_subset_subsumed:                 0
% 1.84/1.00  sim_fw_subsumed:                        0
% 1.84/1.00  sim_bw_subsumed:                        2
% 1.84/1.00  sim_fw_subsumption_res:                 5
% 1.84/1.00  sim_bw_subsumption_res:                 0
% 1.84/1.00  sim_tautology_del:                      1
% 1.84/1.00  sim_eq_tautology_del:                   0
% 1.84/1.00  sim_eq_res_simp:                        2
% 1.84/1.00  sim_fw_demodulated:                     0
% 1.84/1.00  sim_bw_demodulated:                     0
% 1.84/1.00  sim_light_normalised:                   5
% 1.84/1.00  sim_joinable_taut:                      0
% 1.84/1.00  sim_joinable_simp:                      0
% 1.84/1.00  sim_ac_normalised:                      0
% 1.84/1.00  sim_smt_subsumption:                    0
% 1.84/1.00  
%------------------------------------------------------------------------------
