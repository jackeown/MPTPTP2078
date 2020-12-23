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
% DateTime   : Thu Dec  3 12:29:18 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  216 (2030 expanded)
%              Number of clauses        :  138 ( 454 expanded)
%              Number of leaves         :   16 ( 562 expanded)
%              Depth                    :   33
%              Number of atoms          : 1391 (16892 expanded)
%              Number of equality atoms :  204 ( 535 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f43,f42,f41])).

fof(f67,plain,(
    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f67,f50])).

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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f23])).

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
    inference(cnf_transformation,[],[f24])).

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
    inference(definition_unfolding,[],[f54,f50,f50,f50])).

fof(f72,plain,
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f29])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f68,f50])).

fof(f65,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f25])).

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
    inference(cnf_transformation,[],[f26])).

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
    inference(definition_unfolding,[],[f56,f50,f50,f50])).

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
    inference(cnf_transformation,[],[f24])).

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
    inference(definition_unfolding,[],[f53,f50,f50,f50])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(definition_unfolding,[],[f66,f50])).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f31])).

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
    inference(cnf_transformation,[],[f32])).

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
    inference(definition_unfolding,[],[f61,f50,f50,f50,f50])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(definition_unfolding,[],[f69,f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f27])).

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
    inference(cnf_transformation,[],[f28])).

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
    inference(definition_unfolding,[],[f58,f50,f50,f50,f50])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK0(X0),X0)
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f35])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f46,plain,(
    ! [X0] : ~ v1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f44])).

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
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

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
    inference(cnf_transformation,[],[f73])).

cnf(c_16,negated_conjecture,
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_199,plain,
    ( ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
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
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

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
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_392,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_396,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_26,c_24])).

cnf(c_673,plain,
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
    inference(resolution_lifted,[status(thm)],[c_199,c_396])).

cnf(c_674,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_676,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_18])).

cnf(c_677,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_676])).

cnf(c_713,plain,
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
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_677])).

cnf(c_714,plain,
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
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_713])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_73,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_718,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_714,c_26,c_24,c_73])).

cnf(c_719,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(renaming,[status(thm)],[c_718])).

cnf(c_20,negated_conjecture,
    ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1403,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_719,c_20])).

cnf(c_1404,plain,
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
    inference(unflattening,[status(thm)],[c_1403])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1408,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1404,c_23])).

cnf(c_1409,plain,
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
    inference(renaming,[status(thm)],[c_1408])).

cnf(c_1644,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_1409])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_440,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_441,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_440])).

cnf(c_811,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_441])).

cnf(c_812,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_811])).

cnf(c_70,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_814,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_812,c_26,c_24,c_70,c_73])).

cnf(c_2526,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK1) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_1644,c_814])).

cnf(c_2527,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,u1_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
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
    inference(cnf_transformation,[],[f75])).

cnf(c_863,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_441])).

cnf(c_864,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v2_struct_0(sK1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_863])).

cnf(c_868,plain,
    ( v4_orders_2(k3_yellow19(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
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
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_868])).

cnf(c_1328,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_orders_2(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_869,c_20])).

cnf(c_1329,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1328])).

cnf(c_1333,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1329,c_23])).

cnf(c_1334,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1333])).

cnf(c_1720,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1334])).

cnf(c_2479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK1) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_1720,c_814])).

cnf(c_2480,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | v4_orders_2(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_2479])).

cnf(c_2792,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
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
    inference(cnf_transformation,[],[f74])).

cnf(c_896,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_441])).

cnf(c_897,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v2_struct_0(sK1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_896])).

cnf(c_901,plain,
    ( ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
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
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_901])).

cnf(c_1298,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_902,c_20])).

cnf(c_1299,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1298])).

cnf(c_1303,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1299,c_23])).

cnf(c_1304,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1303])).

cnf(c_1743,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1304])).

cnf(c_2463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK1) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_1743,c_814])).

cnf(c_2464,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | ~ v2_struct_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_2463])).

cnf(c_3146,plain,
    ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(resolution_lifted,[status(thm)],[c_2792,c_2464])).

cnf(c_4245,plain,
    ( k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) != iProver_top
    | r1_waybel_7(sK1,sK2,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3146])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_822,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_441])).

cnf(c_823,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_822])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_15,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_929,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_441])).

cnf(c_930,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_934,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | v1_xboole_0(X0)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_26])).

cnf(c_935,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))
    | v1_xboole_0(X0)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) = X0 ),
    inference(renaming,[status(thm)],[c_934])).

cnf(c_1109,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v1_xboole_0(X0)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_935])).

cnf(c_1110,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | v1_xboole_0(sK2)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_1109])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1112,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1110,c_23,c_21,c_20,c_19])).

cnf(c_4342,plain,
    ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | r1_waybel_7(sK1,sK2,sK3) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4245,c_823,c_1112])).

cnf(c_4343,plain,
    ( r1_waybel_7(sK1,sK2,sK3) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4342])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_827,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_441])).

cnf(c_828,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | v7_waybel_0(k3_yellow19(sK1,X1,X0))
    | v2_struct_0(sK1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_827])).

cnf(c_832,plain,
    ( v7_waybel_0(k3_yellow19(sK1,X1,X0))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_828,c_26])).

cnf(c_833,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | v7_waybel_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_832])).

cnf(c_1012,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v7_waybel_0(k3_yellow19(sK1,X1,X0))
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
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v7_waybel_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(X1))) = X0 ),
    inference(unflattening,[status(thm)],[c_1012])).

cnf(c_1265,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v7_waybel_0(k3_yellow19(sK1,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | u1_struct_0(k3_lattice3(k1_lattice3(X1))) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1013,c_20])).

cnf(c_1266,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2 ),
    inference(unflattening,[status(thm)],[c_1265])).

cnf(c_1270,plain,
    ( v1_xboole_0(X0)
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1266,c_23])).

cnf(c_1271,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2 ),
    inference(renaming,[status(thm)],[c_1270])).

cnf(c_1766,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1271])).

cnf(c_2444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2
    | u1_struct_0(sK1) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_1766,c_814])).

cnf(c_2445,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))) = sK2 ),
    inference(unflattening,[status(thm)],[c_2444])).

cnf(c_4250,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))) = sK2
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2445])).

cnf(c_4288,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) = sK2
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4250,c_823])).

cnf(c_4289,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) = sK2
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4288])).

cnf(c_4254,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4256,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ v1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_994,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_995,plain,
    ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(X0))
    | X0 = sK0(X0) ),
    inference(unflattening,[status(thm)],[c_994])).

cnf(c_999,plain,
    ( X0 = sK0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_995,c_1])).

cnf(c_4264,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4256,c_999])).

cnf(c_1005,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != X0
    | sK0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_1006,plain,
    ( sK0(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != sK2 ),
    inference(unflattening,[status(thm)],[c_1005])).

cnf(c_4269,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != sK2 ),
    inference(demodulation,[status(thm)],[c_1006,c_999])).

cnf(c_4294,plain,
    ( v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4289,c_4254,c_4264,c_4269])).

cnf(c_17,negated_conjecture,
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_201,plain,
    ( r1_waybel_7(sK1,sK2,sK3)
    | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
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
    inference(cnf_transformation,[],[f59])).

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
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_359,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_363,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r3_waybel_9(sK1,X0,X1)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_26,c_24])).

cnf(c_647,plain,
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
    inference(resolution_lifted,[status(thm)],[c_201,c_363])).

cnf(c_648,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_650,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | r1_waybel_7(sK1,sK2,sK3)
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_18])).

cnf(c_651,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_650])).

cnf(c_761,plain,
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
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_651])).

cnf(c_762,plain,
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
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK1)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(unflattening,[status(thm)],[c_761])).

cnf(c_766,plain,
    ( v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_762,c_26,c_24,c_73])).

cnf(c_767,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
    inference(renaming,[status(thm)],[c_766])).

cnf(c_1358,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_767,c_20])).

cnf(c_1359,plain,
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
    inference(unflattening,[status(thm)],[c_1358])).

cnf(c_1363,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1359,c_23])).

cnf(c_1364,plain,
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
    inference(renaming,[status(thm)],[c_1363])).

cnf(c_1682,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_1364])).

cnf(c_2495,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK1) != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_1682,c_814])).

cnf(c_2496,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,u1_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_2495])).

cnf(c_2819,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(resolution_lifted,[status(thm)],[c_2496,c_2480])).

cnf(c_3122,plain,
    ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
    | r1_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(resolution_lifted,[status(thm)],[c_2819,c_2464])).

cnf(c_4246,plain,
    ( k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) = iProver_top
    | r1_waybel_7(sK1,sK2,sK3) = iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3122])).

cnf(c_4334,plain,
    ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | r1_waybel_7(sK1,sK2,sK3) = iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4246,c_823,c_1112])).

cnf(c_4335,plain,
    ( r1_waybel_7(sK1,sK2,sK3) = iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4334])).

cnf(c_4340,plain,
    ( r1_waybel_7(sK1,sK2,sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4335,c_4294,c_4254,c_4264])).

cnf(c_4348,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4343,c_4294,c_4254,c_4264,c_4340])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.05/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.05/0.98  
% 2.05/0.98  ------  iProver source info
% 2.05/0.98  
% 2.05/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.05/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.05/0.98  git: non_committed_changes: false
% 2.05/0.98  git: last_make_outside_of_git: false
% 2.05/0.98  
% 2.05/0.98  ------ 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options
% 2.05/0.98  
% 2.05/0.98  --out_options                           all
% 2.05/0.98  --tptp_safe_out                         true
% 2.05/0.98  --problem_path                          ""
% 2.05/0.98  --include_path                          ""
% 2.05/0.98  --clausifier                            res/vclausify_rel
% 2.05/0.98  --clausifier_options                    --mode clausify
% 2.05/0.98  --stdin                                 false
% 2.05/0.98  --stats_out                             all
% 2.05/0.98  
% 2.05/0.98  ------ General Options
% 2.05/0.98  
% 2.05/0.98  --fof                                   false
% 2.05/0.98  --time_out_real                         305.
% 2.05/0.98  --time_out_virtual                      -1.
% 2.05/0.98  --symbol_type_check                     false
% 2.05/0.98  --clausify_out                          false
% 2.05/0.98  --sig_cnt_out                           false
% 2.05/0.98  --trig_cnt_out                          false
% 2.05/0.98  --trig_cnt_out_tolerance                1.
% 2.05/0.98  --trig_cnt_out_sk_spl                   false
% 2.05/0.98  --abstr_cl_out                          false
% 2.05/0.98  
% 2.05/0.98  ------ Global Options
% 2.05/0.98  
% 2.05/0.98  --schedule                              default
% 2.05/0.98  --add_important_lit                     false
% 2.05/0.98  --prop_solver_per_cl                    1000
% 2.05/0.98  --min_unsat_core                        false
% 2.05/0.98  --soft_assumptions                      false
% 2.05/0.98  --soft_lemma_size                       3
% 2.05/0.98  --prop_impl_unit_size                   0
% 2.05/0.98  --prop_impl_unit                        []
% 2.05/0.98  --share_sel_clauses                     true
% 2.05/0.98  --reset_solvers                         false
% 2.05/0.98  --bc_imp_inh                            [conj_cone]
% 2.05/0.98  --conj_cone_tolerance                   3.
% 2.05/0.98  --extra_neg_conj                        none
% 2.05/0.98  --large_theory_mode                     true
% 2.05/0.98  --prolific_symb_bound                   200
% 2.05/0.98  --lt_threshold                          2000
% 2.05/0.98  --clause_weak_htbl                      true
% 2.05/0.98  --gc_record_bc_elim                     false
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing Options
% 2.05/0.98  
% 2.05/0.98  --preprocessing_flag                    true
% 2.05/0.98  --time_out_prep_mult                    0.1
% 2.05/0.98  --splitting_mode                        input
% 2.05/0.98  --splitting_grd                         true
% 2.05/0.98  --splitting_cvd                         false
% 2.05/0.98  --splitting_cvd_svl                     false
% 2.05/0.98  --splitting_nvd                         32
% 2.05/0.98  --sub_typing                            true
% 2.05/0.98  --prep_gs_sim                           true
% 2.05/0.98  --prep_unflatten                        true
% 2.05/0.98  --prep_res_sim                          true
% 2.05/0.98  --prep_upred                            true
% 2.05/0.98  --prep_sem_filter                       exhaustive
% 2.05/0.98  --prep_sem_filter_out                   false
% 2.05/0.98  --pred_elim                             true
% 2.05/0.98  --res_sim_input                         true
% 2.05/0.98  --eq_ax_congr_red                       true
% 2.05/0.98  --pure_diseq_elim                       true
% 2.05/0.98  --brand_transform                       false
% 2.05/0.98  --non_eq_to_eq                          false
% 2.05/0.98  --prep_def_merge                        true
% 2.05/0.98  --prep_def_merge_prop_impl              false
% 2.05/0.98  --prep_def_merge_mbd                    true
% 2.05/0.98  --prep_def_merge_tr_red                 false
% 2.05/0.98  --prep_def_merge_tr_cl                  false
% 2.05/0.98  --smt_preprocessing                     true
% 2.05/0.98  --smt_ac_axioms                         fast
% 2.05/0.98  --preprocessed_out                      false
% 2.05/0.98  --preprocessed_stats                    false
% 2.05/0.98  
% 2.05/0.98  ------ Abstraction refinement Options
% 2.05/0.98  
% 2.05/0.98  --abstr_ref                             []
% 2.05/0.98  --abstr_ref_prep                        false
% 2.05/0.98  --abstr_ref_until_sat                   false
% 2.05/0.98  --abstr_ref_sig_restrict                funpre
% 2.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.98  --abstr_ref_under                       []
% 2.05/0.98  
% 2.05/0.98  ------ SAT Options
% 2.05/0.98  
% 2.05/0.98  --sat_mode                              false
% 2.05/0.98  --sat_fm_restart_options                ""
% 2.05/0.98  --sat_gr_def                            false
% 2.05/0.98  --sat_epr_types                         true
% 2.05/0.98  --sat_non_cyclic_types                  false
% 2.05/0.98  --sat_finite_models                     false
% 2.05/0.98  --sat_fm_lemmas                         false
% 2.05/0.98  --sat_fm_prep                           false
% 2.05/0.98  --sat_fm_uc_incr                        true
% 2.05/0.98  --sat_out_model                         small
% 2.05/0.98  --sat_out_clauses                       false
% 2.05/0.98  
% 2.05/0.98  ------ QBF Options
% 2.05/0.98  
% 2.05/0.98  --qbf_mode                              false
% 2.05/0.98  --qbf_elim_univ                         false
% 2.05/0.98  --qbf_dom_inst                          none
% 2.05/0.98  --qbf_dom_pre_inst                      false
% 2.05/0.98  --qbf_sk_in                             false
% 2.05/0.98  --qbf_pred_elim                         true
% 2.05/0.98  --qbf_split                             512
% 2.05/0.98  
% 2.05/0.98  ------ BMC1 Options
% 2.05/0.98  
% 2.05/0.98  --bmc1_incremental                      false
% 2.05/0.98  --bmc1_axioms                           reachable_all
% 2.05/0.98  --bmc1_min_bound                        0
% 2.05/0.98  --bmc1_max_bound                        -1
% 2.05/0.98  --bmc1_max_bound_default                -1
% 2.05/0.98  --bmc1_symbol_reachability              true
% 2.05/0.98  --bmc1_property_lemmas                  false
% 2.05/0.98  --bmc1_k_induction                      false
% 2.05/0.98  --bmc1_non_equiv_states                 false
% 2.05/0.98  --bmc1_deadlock                         false
% 2.05/0.98  --bmc1_ucm                              false
% 2.05/0.98  --bmc1_add_unsat_core                   none
% 2.05/0.98  --bmc1_unsat_core_children              false
% 2.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.98  --bmc1_out_stat                         full
% 2.05/0.98  --bmc1_ground_init                      false
% 2.05/0.98  --bmc1_pre_inst_next_state              false
% 2.05/0.98  --bmc1_pre_inst_state                   false
% 2.05/0.98  --bmc1_pre_inst_reach_state             false
% 2.05/0.98  --bmc1_out_unsat_core                   false
% 2.05/0.98  --bmc1_aig_witness_out                  false
% 2.05/0.98  --bmc1_verbose                          false
% 2.05/0.98  --bmc1_dump_clauses_tptp                false
% 2.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.98  --bmc1_dump_file                        -
% 2.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.98  --bmc1_ucm_extend_mode                  1
% 2.05/0.98  --bmc1_ucm_init_mode                    2
% 2.05/0.98  --bmc1_ucm_cone_mode                    none
% 2.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.98  --bmc1_ucm_relax_model                  4
% 2.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.98  --bmc1_ucm_layered_model                none
% 2.05/0.98  --bmc1_ucm_max_lemma_size               10
% 2.05/0.98  
% 2.05/0.98  ------ AIG Options
% 2.05/0.98  
% 2.05/0.98  --aig_mode                              false
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation Options
% 2.05/0.98  
% 2.05/0.98  --instantiation_flag                    true
% 2.05/0.98  --inst_sos_flag                         false
% 2.05/0.98  --inst_sos_phase                        true
% 2.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel_side                     num_symb
% 2.05/0.98  --inst_solver_per_active                1400
% 2.05/0.98  --inst_solver_calls_frac                1.
% 2.05/0.98  --inst_passive_queue_type               priority_queues
% 2.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.98  --inst_passive_queues_freq              [25;2]
% 2.05/0.98  --inst_dismatching                      true
% 2.05/0.98  --inst_eager_unprocessed_to_passive     true
% 2.05/0.98  --inst_prop_sim_given                   true
% 2.05/0.98  --inst_prop_sim_new                     false
% 2.05/0.98  --inst_subs_new                         false
% 2.05/0.98  --inst_eq_res_simp                      false
% 2.05/0.98  --inst_subs_given                       false
% 2.05/0.98  --inst_orphan_elimination               true
% 2.05/0.98  --inst_learning_loop_flag               true
% 2.05/0.98  --inst_learning_start                   3000
% 2.05/0.98  --inst_learning_factor                  2
% 2.05/0.98  --inst_start_prop_sim_after_learn       3
% 2.05/0.98  --inst_sel_renew                        solver
% 2.05/0.98  --inst_lit_activity_flag                true
% 2.05/0.98  --inst_restr_to_given                   false
% 2.05/0.98  --inst_activity_threshold               500
% 2.05/0.98  --inst_out_proof                        true
% 2.05/0.98  
% 2.05/0.98  ------ Resolution Options
% 2.05/0.98  
% 2.05/0.98  --resolution_flag                       true
% 2.05/0.98  --res_lit_sel                           adaptive
% 2.05/0.98  --res_lit_sel_side                      none
% 2.05/0.98  --res_ordering                          kbo
% 2.05/0.98  --res_to_prop_solver                    active
% 2.05/0.98  --res_prop_simpl_new                    false
% 2.05/0.98  --res_prop_simpl_given                  true
% 2.05/0.98  --res_passive_queue_type                priority_queues
% 2.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.98  --res_passive_queues_freq               [15;5]
% 2.05/0.98  --res_forward_subs                      full
% 2.05/0.98  --res_backward_subs                     full
% 2.05/0.98  --res_forward_subs_resolution           true
% 2.05/0.98  --res_backward_subs_resolution          true
% 2.05/0.98  --res_orphan_elimination                true
% 2.05/0.98  --res_time_limit                        2.
% 2.05/0.98  --res_out_proof                         true
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Options
% 2.05/0.98  
% 2.05/0.98  --superposition_flag                    true
% 2.05/0.98  --sup_passive_queue_type                priority_queues
% 2.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.98  --demod_completeness_check              fast
% 2.05/0.98  --demod_use_ground                      true
% 2.05/0.98  --sup_to_prop_solver                    passive
% 2.05/0.98  --sup_prop_simpl_new                    true
% 2.05/0.98  --sup_prop_simpl_given                  true
% 2.05/0.98  --sup_fun_splitting                     false
% 2.05/0.98  --sup_smt_interval                      50000
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Simplification Setup
% 2.05/0.98  
% 2.05/0.98  --sup_indices_passive                   []
% 2.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_full_bw                           [BwDemod]
% 2.05/0.98  --sup_immed_triv                        [TrivRules]
% 2.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_immed_bw_main                     []
% 2.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  
% 2.05/0.98  ------ Combination Options
% 2.05/0.98  
% 2.05/0.98  --comb_res_mult                         3
% 2.05/0.98  --comb_sup_mult                         2
% 2.05/0.98  --comb_inst_mult                        10
% 2.05/0.98  
% 2.05/0.98  ------ Debug Options
% 2.05/0.98  
% 2.05/0.98  --dbg_backtrace                         false
% 2.05/0.98  --dbg_dump_prop_clauses                 false
% 2.05/0.98  --dbg_dump_prop_clauses_file            -
% 2.05/0.98  --dbg_out_stat                          false
% 2.05/0.98  ------ Parsing...
% 2.05/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.05/0.98  ------ Proving...
% 2.05/0.98  ------ Problem Properties 
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  clauses                                 16
% 2.05/0.98  conjectures                             2
% 2.05/0.98  EPR                                     0
% 2.05/0.98  Horn                                    12
% 2.05/0.98  unary                                   7
% 2.05/0.98  binary                                  1
% 2.05/0.98  lits                                    57
% 2.05/0.98  lits eq                                 21
% 2.05/0.98  fd_pure                                 0
% 2.05/0.98  fd_pseudo                               0
% 2.05/0.98  fd_cond                                 0
% 2.05/0.98  fd_pseudo_cond                          0
% 2.05/0.98  AC symbols                              0
% 2.05/0.98  
% 2.05/0.98  ------ Schedule dynamic 5 is on 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  ------ 
% 2.05/0.98  Current options:
% 2.05/0.98  ------ 
% 2.05/0.98  
% 2.05/0.98  ------ Input Options
% 2.05/0.98  
% 2.05/0.98  --out_options                           all
% 2.05/0.98  --tptp_safe_out                         true
% 2.05/0.98  --problem_path                          ""
% 2.05/0.98  --include_path                          ""
% 2.05/0.98  --clausifier                            res/vclausify_rel
% 2.05/0.98  --clausifier_options                    --mode clausify
% 2.05/0.98  --stdin                                 false
% 2.05/0.98  --stats_out                             all
% 2.05/0.98  
% 2.05/0.98  ------ General Options
% 2.05/0.98  
% 2.05/0.98  --fof                                   false
% 2.05/0.98  --time_out_real                         305.
% 2.05/0.98  --time_out_virtual                      -1.
% 2.05/0.98  --symbol_type_check                     false
% 2.05/0.98  --clausify_out                          false
% 2.05/0.98  --sig_cnt_out                           false
% 2.05/0.98  --trig_cnt_out                          false
% 2.05/0.98  --trig_cnt_out_tolerance                1.
% 2.05/0.98  --trig_cnt_out_sk_spl                   false
% 2.05/0.98  --abstr_cl_out                          false
% 2.05/0.98  
% 2.05/0.98  ------ Global Options
% 2.05/0.98  
% 2.05/0.98  --schedule                              default
% 2.05/0.98  --add_important_lit                     false
% 2.05/0.98  --prop_solver_per_cl                    1000
% 2.05/0.98  --min_unsat_core                        false
% 2.05/0.98  --soft_assumptions                      false
% 2.05/0.98  --soft_lemma_size                       3
% 2.05/0.98  --prop_impl_unit_size                   0
% 2.05/0.98  --prop_impl_unit                        []
% 2.05/0.98  --share_sel_clauses                     true
% 2.05/0.98  --reset_solvers                         false
% 2.05/0.98  --bc_imp_inh                            [conj_cone]
% 2.05/0.98  --conj_cone_tolerance                   3.
% 2.05/0.98  --extra_neg_conj                        none
% 2.05/0.98  --large_theory_mode                     true
% 2.05/0.98  --prolific_symb_bound                   200
% 2.05/0.98  --lt_threshold                          2000
% 2.05/0.98  --clause_weak_htbl                      true
% 2.05/0.98  --gc_record_bc_elim                     false
% 2.05/0.98  
% 2.05/0.98  ------ Preprocessing Options
% 2.05/0.98  
% 2.05/0.98  --preprocessing_flag                    true
% 2.05/0.98  --time_out_prep_mult                    0.1
% 2.05/0.98  --splitting_mode                        input
% 2.05/0.98  --splitting_grd                         true
% 2.05/0.98  --splitting_cvd                         false
% 2.05/0.98  --splitting_cvd_svl                     false
% 2.05/0.98  --splitting_nvd                         32
% 2.05/0.98  --sub_typing                            true
% 2.05/0.98  --prep_gs_sim                           true
% 2.05/0.98  --prep_unflatten                        true
% 2.05/0.98  --prep_res_sim                          true
% 2.05/0.98  --prep_upred                            true
% 2.05/0.98  --prep_sem_filter                       exhaustive
% 2.05/0.98  --prep_sem_filter_out                   false
% 2.05/0.98  --pred_elim                             true
% 2.05/0.98  --res_sim_input                         true
% 2.05/0.98  --eq_ax_congr_red                       true
% 2.05/0.98  --pure_diseq_elim                       true
% 2.05/0.98  --brand_transform                       false
% 2.05/0.98  --non_eq_to_eq                          false
% 2.05/0.98  --prep_def_merge                        true
% 2.05/0.98  --prep_def_merge_prop_impl              false
% 2.05/0.98  --prep_def_merge_mbd                    true
% 2.05/0.98  --prep_def_merge_tr_red                 false
% 2.05/0.98  --prep_def_merge_tr_cl                  false
% 2.05/0.98  --smt_preprocessing                     true
% 2.05/0.98  --smt_ac_axioms                         fast
% 2.05/0.98  --preprocessed_out                      false
% 2.05/0.98  --preprocessed_stats                    false
% 2.05/0.98  
% 2.05/0.98  ------ Abstraction refinement Options
% 2.05/0.98  
% 2.05/0.98  --abstr_ref                             []
% 2.05/0.98  --abstr_ref_prep                        false
% 2.05/0.98  --abstr_ref_until_sat                   false
% 2.05/0.98  --abstr_ref_sig_restrict                funpre
% 2.05/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.05/0.98  --abstr_ref_under                       []
% 2.05/0.98  
% 2.05/0.98  ------ SAT Options
% 2.05/0.98  
% 2.05/0.98  --sat_mode                              false
% 2.05/0.98  --sat_fm_restart_options                ""
% 2.05/0.98  --sat_gr_def                            false
% 2.05/0.98  --sat_epr_types                         true
% 2.05/0.98  --sat_non_cyclic_types                  false
% 2.05/0.98  --sat_finite_models                     false
% 2.05/0.98  --sat_fm_lemmas                         false
% 2.05/0.98  --sat_fm_prep                           false
% 2.05/0.98  --sat_fm_uc_incr                        true
% 2.05/0.98  --sat_out_model                         small
% 2.05/0.98  --sat_out_clauses                       false
% 2.05/0.98  
% 2.05/0.98  ------ QBF Options
% 2.05/0.98  
% 2.05/0.98  --qbf_mode                              false
% 2.05/0.98  --qbf_elim_univ                         false
% 2.05/0.98  --qbf_dom_inst                          none
% 2.05/0.98  --qbf_dom_pre_inst                      false
% 2.05/0.98  --qbf_sk_in                             false
% 2.05/0.98  --qbf_pred_elim                         true
% 2.05/0.98  --qbf_split                             512
% 2.05/0.98  
% 2.05/0.98  ------ BMC1 Options
% 2.05/0.98  
% 2.05/0.98  --bmc1_incremental                      false
% 2.05/0.98  --bmc1_axioms                           reachable_all
% 2.05/0.98  --bmc1_min_bound                        0
% 2.05/0.98  --bmc1_max_bound                        -1
% 2.05/0.98  --bmc1_max_bound_default                -1
% 2.05/0.98  --bmc1_symbol_reachability              true
% 2.05/0.98  --bmc1_property_lemmas                  false
% 2.05/0.98  --bmc1_k_induction                      false
% 2.05/0.98  --bmc1_non_equiv_states                 false
% 2.05/0.98  --bmc1_deadlock                         false
% 2.05/0.98  --bmc1_ucm                              false
% 2.05/0.98  --bmc1_add_unsat_core                   none
% 2.05/0.98  --bmc1_unsat_core_children              false
% 2.05/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.05/0.98  --bmc1_out_stat                         full
% 2.05/0.98  --bmc1_ground_init                      false
% 2.05/0.98  --bmc1_pre_inst_next_state              false
% 2.05/0.98  --bmc1_pre_inst_state                   false
% 2.05/0.98  --bmc1_pre_inst_reach_state             false
% 2.05/0.98  --bmc1_out_unsat_core                   false
% 2.05/0.98  --bmc1_aig_witness_out                  false
% 2.05/0.98  --bmc1_verbose                          false
% 2.05/0.98  --bmc1_dump_clauses_tptp                false
% 2.05/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.05/0.98  --bmc1_dump_file                        -
% 2.05/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.05/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.05/0.98  --bmc1_ucm_extend_mode                  1
% 2.05/0.98  --bmc1_ucm_init_mode                    2
% 2.05/0.98  --bmc1_ucm_cone_mode                    none
% 2.05/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.05/0.98  --bmc1_ucm_relax_model                  4
% 2.05/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.05/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.05/0.98  --bmc1_ucm_layered_model                none
% 2.05/0.98  --bmc1_ucm_max_lemma_size               10
% 2.05/0.98  
% 2.05/0.98  ------ AIG Options
% 2.05/0.98  
% 2.05/0.98  --aig_mode                              false
% 2.05/0.98  
% 2.05/0.98  ------ Instantiation Options
% 2.05/0.98  
% 2.05/0.98  --instantiation_flag                    true
% 2.05/0.98  --inst_sos_flag                         false
% 2.05/0.98  --inst_sos_phase                        true
% 2.05/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.05/0.98  --inst_lit_sel_side                     none
% 2.05/0.98  --inst_solver_per_active                1400
% 2.05/0.98  --inst_solver_calls_frac                1.
% 2.05/0.98  --inst_passive_queue_type               priority_queues
% 2.05/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.05/0.98  --inst_passive_queues_freq              [25;2]
% 2.05/0.98  --inst_dismatching                      true
% 2.05/0.98  --inst_eager_unprocessed_to_passive     true
% 2.05/0.98  --inst_prop_sim_given                   true
% 2.05/0.98  --inst_prop_sim_new                     false
% 2.05/0.98  --inst_subs_new                         false
% 2.05/0.98  --inst_eq_res_simp                      false
% 2.05/0.98  --inst_subs_given                       false
% 2.05/0.98  --inst_orphan_elimination               true
% 2.05/0.98  --inst_learning_loop_flag               true
% 2.05/0.98  --inst_learning_start                   3000
% 2.05/0.98  --inst_learning_factor                  2
% 2.05/0.98  --inst_start_prop_sim_after_learn       3
% 2.05/0.98  --inst_sel_renew                        solver
% 2.05/0.98  --inst_lit_activity_flag                true
% 2.05/0.98  --inst_restr_to_given                   false
% 2.05/0.98  --inst_activity_threshold               500
% 2.05/0.98  --inst_out_proof                        true
% 2.05/0.98  
% 2.05/0.98  ------ Resolution Options
% 2.05/0.98  
% 2.05/0.98  --resolution_flag                       false
% 2.05/0.98  --res_lit_sel                           adaptive
% 2.05/0.98  --res_lit_sel_side                      none
% 2.05/0.98  --res_ordering                          kbo
% 2.05/0.98  --res_to_prop_solver                    active
% 2.05/0.98  --res_prop_simpl_new                    false
% 2.05/0.98  --res_prop_simpl_given                  true
% 2.05/0.98  --res_passive_queue_type                priority_queues
% 2.05/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.05/0.98  --res_passive_queues_freq               [15;5]
% 2.05/0.98  --res_forward_subs                      full
% 2.05/0.98  --res_backward_subs                     full
% 2.05/0.98  --res_forward_subs_resolution           true
% 2.05/0.98  --res_backward_subs_resolution          true
% 2.05/0.98  --res_orphan_elimination                true
% 2.05/0.98  --res_time_limit                        2.
% 2.05/0.98  --res_out_proof                         true
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Options
% 2.05/0.98  
% 2.05/0.98  --superposition_flag                    true
% 2.05/0.98  --sup_passive_queue_type                priority_queues
% 2.05/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.05/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.05/0.98  --demod_completeness_check              fast
% 2.05/0.98  --demod_use_ground                      true
% 2.05/0.98  --sup_to_prop_solver                    passive
% 2.05/0.98  --sup_prop_simpl_new                    true
% 2.05/0.98  --sup_prop_simpl_given                  true
% 2.05/0.98  --sup_fun_splitting                     false
% 2.05/0.98  --sup_smt_interval                      50000
% 2.05/0.98  
% 2.05/0.98  ------ Superposition Simplification Setup
% 2.05/0.98  
% 2.05/0.98  --sup_indices_passive                   []
% 2.05/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.05/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.05/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_full_bw                           [BwDemod]
% 2.05/0.98  --sup_immed_triv                        [TrivRules]
% 2.05/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.05/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_immed_bw_main                     []
% 2.05/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.05/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.05/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.05/0.98  
% 2.05/0.98  ------ Combination Options
% 2.05/0.98  
% 2.05/0.98  --comb_res_mult                         3
% 2.05/0.98  --comb_sup_mult                         2
% 2.05/0.98  --comb_inst_mult                        10
% 2.05/0.98  
% 2.05/0.98  ------ Debug Options
% 2.05/0.98  
% 2.05/0.98  --dbg_backtrace                         false
% 2.05/0.98  --dbg_dump_prop_clauses                 false
% 2.05/0.98  --dbg_dump_prop_clauses_file            -
% 2.05/0.98  --dbg_out_stat                          false
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  ------ Proving...
% 2.05/0.98  
% 2.05/0.98  
% 2.05/0.98  % SZS status Theorem for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98   Resolution empty clause
% 2.05/0.98  
% 2.05/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.05/0.98  
% 2.05/0.98  fof(f12,conjecture,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f13,negated_conjecture,(
% 2.05/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.05/0.98    inference(negated_conjecture,[],[f12])).
% 2.05/0.98  
% 2.05/0.98  fof(f33,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f13])).
% 2.05/0.98  
% 2.05/0.98  fof(f34,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f33])).
% 2.05/0.98  
% 2.05/0.98  fof(f39,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.98    inference(nnf_transformation,[],[f34])).
% 2.05/0.98  
% 2.05/0.98  fof(f40,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f39])).
% 2.05/0.98  
% 2.05/0.98  fof(f43,plain,(
% 2.05/0.98    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK3) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3)) & (r1_waybel_7(X0,X1,sK3) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK3)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f42,plain,(
% 2.05/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK2,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2)) & (r1_waybel_7(X0,sK2,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK2),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK2))) )),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f41,plain,(
% 2.05/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK1,X1,X2) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2)) & (r1_waybel_7(sK1,X1,X2) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.05/0.98    introduced(choice_axiom,[])).
% 2.05/0.98  
% 2.05/0.98  fof(f44,plain,(
% 2.05/0.98    (((~r1_waybel_7(sK1,sK2,sK3) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)) & (r1_waybel_7(sK1,sK2,sK3) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.05/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f43,f42,f41])).
% 2.05/0.98  
% 2.05/0.98  fof(f67,plain,(
% 2.05/0.98    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 2.05/0.98    inference(cnf_transformation,[],[f44])).
% 2.05/0.98  
% 2.05/0.98  fof(f5,axiom,(
% 2.05/0.98    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f50,plain,(
% 2.05/0.98    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.05/0.98    inference(cnf_transformation,[],[f5])).
% 2.05/0.98  
% 2.05/0.98  fof(f82,plain,(
% 2.05/0.98    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 2.05/0.98    inference(definition_unfolding,[],[f67,f50])).
% 2.05/0.98  
% 2.05/0.98  fof(f7,axiom,(
% 2.05/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f16,plain,(
% 2.05/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.05/0.98    inference(pure_predicate_removal,[],[f7])).
% 2.05/0.98  
% 2.05/0.98  fof(f23,plain,(
% 2.05/0.98    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f16])).
% 2.05/0.98  
% 2.05/0.98  fof(f24,plain,(
% 2.05/0.98    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f23])).
% 2.05/0.98  
% 2.05/0.98  fof(f54,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f24])).
% 2.05/0.98  
% 2.05/0.98  fof(f73,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(definition_unfolding,[],[f54,f50,f50,f50])).
% 2.05/0.98  
% 2.05/0.98  fof(f72,plain,(
% 2.05/0.98    ~r1_waybel_7(sK1,sK2,sK3) | ~r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)),
% 2.05/0.98    inference(cnf_transformation,[],[f44])).
% 2.05/0.98  
% 2.05/0.98  fof(f10,axiom,(
% 2.05/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f29,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.05/0.98    inference(ennf_transformation,[],[f10])).
% 2.05/0.98  
% 2.05/0.98  fof(f30,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(flattening,[],[f29])).
% 2.05/0.98  
% 2.05/0.98  fof(f38,plain,(
% 2.05/0.98    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.05/0.98    inference(nnf_transformation,[],[f30])).
% 2.05/0.98  
% 2.05/0.98  fof(f60,plain,(
% 2.05/0.98    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f38])).
% 2.05/0.98  
% 2.05/0.98  fof(f63,plain,(
% 2.05/0.98    v2_pre_topc(sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f44])).
% 2.05/0.98  
% 2.05/0.98  fof(f62,plain,(
% 2.05/0.98    ~v2_struct_0(sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f44])).
% 2.05/0.98  
% 2.05/0.98  fof(f64,plain,(
% 2.05/0.98    l1_pre_topc(sK1)),
% 2.05/0.98    inference(cnf_transformation,[],[f44])).
% 2.05/0.98  
% 2.05/0.98  fof(f70,plain,(
% 2.05/0.98    m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.05/0.98    inference(cnf_transformation,[],[f44])).
% 2.05/0.98  
% 2.05/0.98  fof(f3,axiom,(
% 2.05/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.05/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.98  
% 2.05/0.98  fof(f19,plain,(
% 2.05/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.05/0.98    inference(ennf_transformation,[],[f3])).
% 2.05/0.98  
% 2.05/0.98  fof(f48,plain,(
% 2.05/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.05/0.98    inference(cnf_transformation,[],[f19])).
% 2.05/0.98  
% 2.05/0.98  fof(f68,plain,(
% 2.05/0.98    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 2.05/0.98    inference(cnf_transformation,[],[f44])).
% 2.05/0.99  
% 2.05/0.99  fof(f81,plain,(
% 2.05/0.99    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 2.05/0.99    inference(definition_unfolding,[],[f68,f50])).
% 2.05/0.99  
% 2.05/0.99  fof(f65,plain,(
% 2.05/0.99    ~v1_xboole_0(sK2)),
% 2.05/0.99    inference(cnf_transformation,[],[f44])).
% 2.05/0.99  
% 2.05/0.99  fof(f4,axiom,(
% 2.05/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f20,plain,(
% 2.05/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f4])).
% 2.05/0.99  
% 2.05/0.99  fof(f21,plain,(
% 2.05/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.05/0.99    inference(flattening,[],[f20])).
% 2.05/0.99  
% 2.05/0.99  fof(f49,plain,(
% 2.05/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f21])).
% 2.05/0.99  
% 2.05/0.99  fof(f8,axiom,(
% 2.05/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f14,plain,(
% 2.05/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.05/0.99    inference(pure_predicate_removal,[],[f8])).
% 2.05/0.99  
% 2.05/0.99  fof(f15,plain,(
% 2.05/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.05/0.99    inference(pure_predicate_removal,[],[f14])).
% 2.05/0.99  
% 2.05/0.99  fof(f25,plain,(
% 2.05/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f15])).
% 2.05/0.99  
% 2.05/0.99  fof(f26,plain,(
% 2.05/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.05/0.99    inference(flattening,[],[f25])).
% 2.05/0.99  
% 2.05/0.99  fof(f56,plain,(
% 2.05/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f26])).
% 2.05/0.99  
% 2.05/0.99  fof(f75,plain,(
% 2.05/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(definition_unfolding,[],[f56,f50,f50,f50])).
% 2.05/0.99  
% 2.05/0.99  fof(f53,plain,(
% 2.05/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f24])).
% 2.05/0.99  
% 2.05/0.99  fof(f74,plain,(
% 2.05/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(definition_unfolding,[],[f53,f50,f50,f50])).
% 2.05/0.99  
% 2.05/0.99  fof(f2,axiom,(
% 2.05/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f18,plain,(
% 2.05/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.05/0.99    inference(ennf_transformation,[],[f2])).
% 2.05/0.99  
% 2.05/0.99  fof(f47,plain,(
% 2.05/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f18])).
% 2.05/0.99  
% 2.05/0.99  fof(f66,plain,(
% 2.05/0.99    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))),
% 2.05/0.99    inference(cnf_transformation,[],[f44])).
% 2.05/0.99  
% 2.05/0.99  fof(f83,plain,(
% 2.05/0.99    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))),
% 2.05/0.99    inference(definition_unfolding,[],[f66,f50])).
% 2.05/0.99  
% 2.05/0.99  fof(f11,axiom,(
% 2.05/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f31,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f11])).
% 2.05/0.99  
% 2.05/0.99  fof(f32,plain,(
% 2.05/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.05/0.99    inference(flattening,[],[f31])).
% 2.05/0.99  
% 2.05/0.99  fof(f61,plain,(
% 2.05/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f32])).
% 2.05/0.99  
% 2.05/0.99  fof(f79,plain,(
% 2.05/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(definition_unfolding,[],[f61,f50,f50,f50,f50])).
% 2.05/0.99  
% 2.05/0.99  fof(f69,plain,(
% 2.05/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))),
% 2.05/0.99    inference(cnf_transformation,[],[f44])).
% 2.05/0.99  
% 2.05/0.99  fof(f80,plain,(
% 2.05/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))),
% 2.05/0.99    inference(definition_unfolding,[],[f69,f50])).
% 2.05/0.99  
% 2.05/0.99  fof(f6,axiom,(
% 2.05/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f22,plain,(
% 2.05/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f6])).
% 2.05/0.99  
% 2.05/0.99  fof(f37,plain,(
% 2.05/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.99    inference(nnf_transformation,[],[f22])).
% 2.05/0.99  
% 2.05/0.99  fof(f52,plain,(
% 2.05/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.05/0.99    inference(cnf_transformation,[],[f37])).
% 2.05/0.99  
% 2.05/0.99  fof(f9,axiom,(
% 2.05/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f17,plain,(
% 2.05/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.05/0.99    inference(pure_predicate_removal,[],[f9])).
% 2.05/0.99  
% 2.05/0.99  fof(f27,plain,(
% 2.05/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.05/0.99    inference(ennf_transformation,[],[f17])).
% 2.05/0.99  
% 2.05/0.99  fof(f28,plain,(
% 2.05/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.05/0.99    inference(flattening,[],[f27])).
% 2.05/0.99  
% 2.05/0.99  fof(f58,plain,(
% 2.05/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f28])).
% 2.05/0.99  
% 2.05/0.99  fof(f77,plain,(
% 2.05/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(definition_unfolding,[],[f58,f50,f50,f50,f50])).
% 2.05/0.99  
% 2.05/0.99  fof(f1,axiom,(
% 2.05/0.99    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.05/0.99  
% 2.05/0.99  fof(f35,plain,(
% 2.05/0.99    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 2.05/0.99    introduced(choice_axiom,[])).
% 2.05/0.99  
% 2.05/0.99  fof(f36,plain,(
% 2.05/0.99    ! [X0] : (~v1_subset_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 2.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f35])).
% 2.05/0.99  
% 2.05/0.99  fof(f45,plain,(
% 2.05/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 2.05/0.99    inference(cnf_transformation,[],[f36])).
% 2.05/0.99  
% 2.05/0.99  fof(f46,plain,(
% 2.05/0.99    ( ! [X0] : (~v1_subset_1(sK0(X0),X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f36])).
% 2.05/0.99  
% 2.05/0.99  fof(f71,plain,(
% 2.05/0.99    r1_waybel_7(sK1,sK2,sK3) | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3)),
% 2.05/0.99    inference(cnf_transformation,[],[f44])).
% 2.05/0.99  
% 2.05/0.99  fof(f59,plain,(
% 2.05/0.99    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.05/0.99    inference(cnf_transformation,[],[f38])).
% 2.05/0.99  
% 2.05/0.99  cnf(c_21,negated_conjecture,
% 2.05/0.99      ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.05/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_7,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | v2_struct_0(X2)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | ~ l1_struct_0(X2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_16,negated_conjecture,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.05/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_199,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.05/0.99      inference(prop_impl,[status(thm)],[c_16]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_13,plain,
% 2.05/0.99      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.05/0.99      | r3_waybel_9(X0,X1,X2)
% 2.05/0.99      | ~ l1_waybel_0(X1,X0)
% 2.05/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.05/0.99      | ~ v2_pre_topc(X0)
% 2.05/0.99      | ~ v7_waybel_0(X1)
% 2.05/0.99      | ~ v4_orders_2(X1)
% 2.05/0.99      | v2_struct_0(X0)
% 2.05/0.99      | v2_struct_0(X1)
% 2.05/0.99      | ~ l1_pre_topc(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_25,negated_conjecture,
% 2.05/0.99      ( v2_pre_topc(sK1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_391,plain,
% 2.05/0.99      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.05/0.99      | r3_waybel_9(X0,X1,X2)
% 2.05/0.99      | ~ l1_waybel_0(X1,X0)
% 2.05/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.05/0.99      | ~ v7_waybel_0(X1)
% 2.05/0.99      | ~ v4_orders_2(X1)
% 2.05/0.99      | v2_struct_0(X0)
% 2.05/0.99      | v2_struct_0(X1)
% 2.05/0.99      | ~ l1_pre_topc(X0)
% 2.05/0.99      | sK1 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_392,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.05/0.99      | r3_waybel_9(sK1,X0,X1)
% 2.05/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.05/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.99      | ~ v7_waybel_0(X0)
% 2.05/0.99      | ~ v4_orders_2(X0)
% 2.05/0.99      | v2_struct_0(X0)
% 2.05/0.99      | v2_struct_0(sK1)
% 2.05/0.99      | ~ l1_pre_topc(sK1) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_391]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_26,negated_conjecture,
% 2.05/0.99      ( ~ v2_struct_0(sK1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_24,negated_conjecture,
% 2.05/0.99      ( l1_pre_topc(sK1) ),
% 2.05/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_396,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.05/0.99      | r3_waybel_9(sK1,X0,X1)
% 2.05/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.05/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.99      | ~ v7_waybel_0(X0)
% 2.05/0.99      | ~ v4_orders_2(X0)
% 2.05/0.99      | v2_struct_0(X0) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_392,c_26,c_24]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_673,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.05/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.99      | ~ v7_waybel_0(X0)
% 2.05/0.99      | ~ v4_orders_2(X0)
% 2.05/0.99      | v2_struct_0(X0)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
% 2.05/0.99      | sK3 != X1
% 2.05/0.99      | sK1 != sK1 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_199,c_396]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_674,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.05/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_673]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_18,negated_conjecture,
% 2.05/0.99      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 2.05/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_676,plain,
% 2.05/0.99      ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_674,c_18]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_677,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_676]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_713,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(X2)
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | ~ l1_struct_0(X2)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
% 2.05/0.99      | sK1 != X2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_677]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_714,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(sK1)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | ~ l1_struct_0(sK1)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_713]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3,plain,
% 2.05/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_73,plain,
% 2.05/0.99      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_718,plain,
% 2.05/0.99      ( v1_xboole_0(X0)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_714,c_26,c_24,c_73]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_719,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_718]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_20,negated_conjecture,
% 2.05/0.99      ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 2.05/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1403,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.05/0.99      | sK2 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_719,c_20]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1404,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | v1_xboole_0(sK2)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_1403]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_23,negated_conjecture,
% 2.05/0.99      ( ~ v1_xboole_0(sK2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1408,plain,
% 2.05/0.99      ( v1_xboole_0(X0)
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1404,c_23]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1409,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_1408]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1644,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | sK2 != sK2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_1409]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4,plain,
% 2.05/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_440,plain,
% 2.05/0.99      ( l1_struct_0(X0) | sK1 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_441,plain,
% 2.05/0.99      ( l1_struct_0(sK1) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_440]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_811,plain,
% 2.05/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_441]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_812,plain,
% 2.05/0.99      ( v2_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_811]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_70,plain,
% 2.05/0.99      ( v2_struct_0(sK1)
% 2.05/0.99      | ~ v1_xboole_0(u1_struct_0(sK1))
% 2.05/0.99      | ~ l1_struct_0(sK1) ),
% 2.05/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_814,plain,
% 2.05/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_812,c_26,c_24,c_70,c_73]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2526,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | u1_struct_0(sK1) != X0
% 2.05/0.99      | sK2 != sK2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_1644,c_814]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2527,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,u1_struct_0(sK1),sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_2526]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_9,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.05/0.99      | v2_struct_0(X2)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | ~ l1_struct_0(X2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_863,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.05/0.99      | v2_struct_0(X2)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | sK1 != X2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_441]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_864,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | v2_struct_0(sK1)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_863]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_868,plain,
% 2.05/0.99      ( v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0) ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_864,c_26]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_869,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_868]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1328,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | v4_orders_2(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.05/0.99      | sK2 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_869,c_20]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1329,plain,
% 2.05/0.99      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | v1_xboole_0(sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_1328]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1333,plain,
% 2.05/0.99      ( v1_xboole_0(X0)
% 2.05/0.99      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1329,c_23]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1334,plain,
% 2.05/0.99      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_1333]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1720,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | sK2 != sK2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_1334]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2479,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | u1_struct_0(sK1) != X0
% 2.05/0.99      | sK2 != sK2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_1720,c_814]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2480,plain,
% 2.05/0.99      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 2.05/0.99      | v4_orders_2(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_2479]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2792,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_2527,c_2480]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_8,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | v2_struct_0(X2)
% 2.05/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | ~ l1_struct_0(X2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_896,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | v2_struct_0(X2)
% 2.05/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | sK1 != X2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_441]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_897,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | v2_struct_0(sK1)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_896]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_901,plain,
% 2.05/0.99      ( ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0) ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_897,c_26]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_902,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_901]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1298,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v2_struct_0(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.05/0.99      | sK2 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_902,c_20]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1299,plain,
% 2.05/0.99      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | v1_xboole_0(sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_1298]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1303,plain,
% 2.05/0.99      ( v1_xboole_0(X0)
% 2.05/0.99      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1299,c_23]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1304,plain,
% 2.05/0.99      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_1303]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1743,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | sK2 != sK2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_1304]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2463,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | u1_struct_0(sK1) != X0
% 2.05/0.99      | sK2 != sK2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_1743,c_814]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2464,plain,
% 2.05/0.99      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 2.05/0.99      | ~ v2_struct_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_2463]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3146,plain,
% 2.05/0.99      ( ~ r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_2792,c_2464]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4245,plain,
% 2.05/0.99      ( k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.05/0.99      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) != iProver_top
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3) != iProver_top
% 2.05/0.99      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_3146]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2,plain,
% 2.05/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_822,plain,
% 2.05/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_441]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_823,plain,
% 2.05/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_822]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_22,negated_conjecture,
% 2.05/0.99      ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
% 2.05/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_15,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.05/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 2.05/0.99      | v2_struct_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | ~ l1_struct_0(X1)
% 2.05/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 2.05/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_929,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.05/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 2.05/0.99      | v2_struct_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 2.05/0.99      | sK1 != X1 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_441]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_930,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 2.05/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))
% 2.05/0.99      | v2_struct_0(sK1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) = X0 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_929]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_934,plain,
% 2.05/0.99      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) = X0 ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_930,c_26]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_935,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 2.05/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) = X0 ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_934]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1109,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X0)) = X0
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.05/0.99      | sK2 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_935]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1110,plain,
% 2.05/0.99      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.05/0.99      | ~ v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 2.05/0.99      | v1_xboole_0(sK2)
% 2.05/0.99      | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_1109]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_19,negated_conjecture,
% 2.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
% 2.05/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1112,plain,
% 2.05/0.99      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_1110,c_23,c_21,c_20,c_19]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4342,plain,
% 2.05/0.99      ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3) != iProver_top
% 2.05/0.99      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_4245,c_823,c_1112]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4343,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,sK2,sK3) != iProver_top
% 2.05/0.99      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 2.05/0.99      inference(equality_resolution_simp,[status(thm)],[c_4342]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_5,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_subset_1(X0,X1) | X0 = X1 ),
% 2.05/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_11,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.05/0.99      | v2_struct_0(X2)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | ~ l1_struct_0(X2) ),
% 2.05/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_827,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.05/0.99      | v2_struct_0(X2)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | sK1 != X2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_441]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_828,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | v2_struct_0(sK1)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_827]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_832,plain,
% 2.05/0.99      ( v7_waybel_0(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0) ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_828,c_26]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_833,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_832]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1012,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | X0 != X2
% 2.05/0.99      | X3 = X2
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X1))) != X3 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_833]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1013,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X1))) = X0 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_1012]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1265,plain,
% 2.05/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,X1,X0))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X1))) = X0
% 2.05/0.99      | sK2 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_1013,c_20]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1266,plain,
% 2.05/0.99      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | v1_xboole_0(sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_1265]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1270,plain,
% 2.05/0.99      ( v1_xboole_0(X0)
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2 ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1266,c_23]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1271,plain,
% 2.05/0.99      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2 ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_1270]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1766,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2
% 2.05/0.99      | sK2 != sK2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_1271]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2444,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2
% 2.05/0.99      | u1_struct_0(sK1) != X0
% 2.05/0.99      | sK2 != sK2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_1766,c_814]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2445,plain,
% 2.05/0.99      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))) = sK2 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_2444]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4250,plain,
% 2.05/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))) = sK2
% 2.05/0.99      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2)) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_2445]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4288,plain,
% 2.05/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.05/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) = sK2
% 2.05/0.99      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_4250,c_823]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4289,plain,
% 2.05/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) = sK2
% 2.05/0.99      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
% 2.05/0.99      inference(equality_resolution_simp,[status(thm)],[c_4288]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4254,plain,
% 2.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1,plain,
% 2.05/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 2.05/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4256,plain,
% 2.05/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_0,plain,
% 2.05/0.99      ( ~ v1_subset_1(sK0(X0),X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_994,plain,
% 2.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.05/0.99      | X1 != X2
% 2.05/0.99      | X1 = X0
% 2.05/0.99      | sK0(X2) != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_995,plain,
% 2.05/0.99      ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) | X0 = sK0(X0) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_994]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_999,plain,
% 2.05/0.99      ( X0 = sK0(X0) ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_995,c_1]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4264,plain,
% 2.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_4256,c_999]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1005,plain,
% 2.05/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != X0
% 2.05/0.99      | sK0(X0) != sK2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_22]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1006,plain,
% 2.05/0.99      ( sK0(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != sK2 ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_1005]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4269,plain,
% 2.05/0.99      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != sK2 ),
% 2.05/0.99      inference(demodulation,[status(thm)],[c_1006,c_999]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4294,plain,
% 2.05/0.99      ( v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
% 2.05/0.99      inference(forward_subsumption_resolution,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_4289,c_4254,c_4264,c_4269]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_17,negated_conjecture,
% 2.05/0.99      ( r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.05/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_201,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | r3_waybel_9(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK3) ),
% 2.05/0.99      inference(prop_impl,[status(thm)],[c_17]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_14,plain,
% 2.05/0.99      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.05/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.05/0.99      | ~ l1_waybel_0(X1,X0)
% 2.05/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.05/0.99      | ~ v2_pre_topc(X0)
% 2.05/0.99      | ~ v7_waybel_0(X1)
% 2.05/0.99      | ~ v4_orders_2(X1)
% 2.05/0.99      | v2_struct_0(X0)
% 2.05/0.99      | v2_struct_0(X1)
% 2.05/0.99      | ~ l1_pre_topc(X0) ),
% 2.05/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_358,plain,
% 2.05/0.99      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.05/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.05/0.99      | ~ l1_waybel_0(X1,X0)
% 2.05/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.05/0.99      | ~ v7_waybel_0(X1)
% 2.05/0.99      | ~ v4_orders_2(X1)
% 2.05/0.99      | v2_struct_0(X0)
% 2.05/0.99      | v2_struct_0(X1)
% 2.05/0.99      | ~ l1_pre_topc(X0)
% 2.05/0.99      | sK1 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_359,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.05/0.99      | ~ r3_waybel_9(sK1,X0,X1)
% 2.05/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.05/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.99      | ~ v7_waybel_0(X0)
% 2.05/0.99      | ~ v4_orders_2(X0)
% 2.05/0.99      | v2_struct_0(X0)
% 2.05/0.99      | v2_struct_0(sK1)
% 2.05/0.99      | ~ l1_pre_topc(sK1) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_363,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.05/0.99      | ~ r3_waybel_9(sK1,X0,X1)
% 2.05/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.05/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.99      | ~ v7_waybel_0(X0)
% 2.05/0.99      | ~ v4_orders_2(X0)
% 2.05/0.99      | v2_struct_0(X0) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_359,c_26,c_24]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_647,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ l1_waybel_0(X0,sK1)
% 2.05/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.05/0.99      | ~ v7_waybel_0(X0)
% 2.05/0.99      | ~ v4_orders_2(X0)
% 2.05/0.99      | v2_struct_0(X0)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != X0
% 2.05/0.99      | sK3 != X1
% 2.05/0.99      | sK1 != sK1 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_201,c_363]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_648,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.05/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_647]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_650,plain,
% 2.05/0.99      ( ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_648,c_18]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_651,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ l1_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2),sK1)
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_650]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_761,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(X2)
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | ~ l1_struct_0(X2)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(X2,X1,X0)
% 2.05/0.99      | sK1 != X2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_651]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_762,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(sK1)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | ~ l1_struct_0(sK1)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_761]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_766,plain,
% 2.05/0.99      ( v1_xboole_0(X0)
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.05/0.99      inference(global_propositional_subsumption,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_762,c_26,c_24,c_73]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_767,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_766]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1358,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.05/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X1)
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X1,X0)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 2.05/0.99      | sK2 != X0 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_767,c_20]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1359,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | v1_xboole_0(sK2)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_1358]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1363,plain,
% 2.05/0.99      ( v1_xboole_0(X0)
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1359,c_23]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1364,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.05/0.99      inference(renaming,[status(thm)],[c_1363]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_1682,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v1_xboole_0(X0)
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | sK2 != sK2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_1364]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2495,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,X0,sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 2.05/0.99      | u1_struct_0(sK1) != X0
% 2.05/0.99      | sK2 != sK2 ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_1682,c_814]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2496,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | ~ v4_orders_2(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,u1_struct_0(sK1),sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
% 2.05/0.99      inference(unflattening,[status(thm)],[c_2495]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_2819,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | v2_struct_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_2496,c_2480]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_3122,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3)
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3)
% 2.05/0.99      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.05/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 2.05/0.99      | ~ v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 2.05/0.99      | k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 2.05/0.99      inference(resolution_lifted,[status(thm)],[c_2819,c_2464]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4246,plain,
% 2.05/0.99      ( k3_yellow19(sK1,u1_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.05/0.99      | r1_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)),sK3) = iProver_top
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3) = iProver_top
% 2.05/0.99      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 2.05/0.99      inference(predicate_to_equality,[status(thm)],[c_3122]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4334,plain,
% 2.05/0.99      ( k3_yellow19(sK1,k2_struct_0(sK1),sK2) != k3_yellow19(sK1,k2_struct_0(sK1),sK2)
% 2.05/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 2.05/0.99      | r1_waybel_7(sK1,sK2,sK3) = iProver_top
% 2.05/0.99      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 2.05/0.99      inference(light_normalisation,[status(thm)],[c_4246,c_823,c_1112]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4335,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,sK2,sK3) = iProver_top
% 2.05/0.99      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 2.05/0.99      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 2.05/0.99      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 2.05/0.99      inference(equality_resolution_simp,[status(thm)],[c_4334]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4340,plain,
% 2.05/0.99      ( r1_waybel_7(sK1,sK2,sK3) = iProver_top ),
% 2.05/0.99      inference(forward_subsumption_resolution,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_4335,c_4294,c_4254,c_4264]) ).
% 2.05/0.99  
% 2.05/0.99  cnf(c_4348,plain,
% 2.05/0.99      ( $false ),
% 2.05/0.99      inference(forward_subsumption_resolution,
% 2.05/0.99                [status(thm)],
% 2.05/0.99                [c_4343,c_4294,c_4254,c_4264,c_4340]) ).
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.05/0.99  
% 2.05/0.99  ------                               Statistics
% 2.05/0.99  
% 2.05/0.99  ------ General
% 2.05/0.99  
% 2.05/0.99  abstr_ref_over_cycles:                  0
% 2.05/0.99  abstr_ref_under_cycles:                 0
% 2.05/0.99  gc_basic_clause_elim:                   0
% 2.05/0.99  forced_gc_time:                         0
% 2.05/0.99  parsing_time:                           0.012
% 2.05/0.99  unif_index_cands_time:                  0.
% 2.05/0.99  unif_index_add_time:                    0.
% 2.05/0.99  orderings_time:                         0.
% 2.05/0.99  out_proof_time:                         0.016
% 2.05/0.99  total_time:                             0.17
% 2.05/0.99  num_of_symbols:                         56
% 2.05/0.99  num_of_terms:                           1166
% 2.05/0.99  
% 2.05/0.99  ------ Preprocessing
% 2.05/0.99  
% 2.05/0.99  num_of_splits:                          0
% 2.05/0.99  num_of_split_atoms:                     0
% 2.05/0.99  num_of_reused_defs:                     0
% 2.05/0.99  num_eq_ax_congr_red:                    4
% 2.05/0.99  num_of_sem_filtered_clauses:            1
% 2.05/0.99  num_of_subtypes:                        0
% 2.05/0.99  monotx_restored_types:                  0
% 2.05/0.99  sat_num_of_epr_types:                   0
% 2.05/0.99  sat_num_of_non_cyclic_types:            0
% 2.05/0.99  sat_guarded_non_collapsed_types:        0
% 2.05/0.99  num_pure_diseq_elim:                    0
% 2.05/0.99  simp_replaced_by:                       0
% 2.05/0.99  res_preprocessed:                       100
% 2.05/0.99  prep_upred:                             0
% 2.05/0.99  prep_unflattend:                        51
% 2.05/0.99  smt_new_axioms:                         0
% 2.05/0.99  pred_elim_cands:                        3
% 2.05/0.99  pred_elim:                              11
% 2.05/0.99  pred_elim_cl:                           9
% 2.05/0.99  pred_elim_cycles:                       20
% 2.05/0.99  merged_defs:                            2
% 2.05/0.99  merged_defs_ncl:                        0
% 2.05/0.99  bin_hyper_res:                          2
% 2.05/0.99  prep_cycles:                            4
% 2.05/0.99  pred_elim_time:                         0.104
% 2.05/0.99  splitting_time:                         0.
% 2.05/0.99  sem_filter_time:                        0.
% 2.05/0.99  monotx_time:                            0.
% 2.05/0.99  subtype_inf_time:                       0.
% 2.05/0.99  
% 2.05/0.99  ------ Problem properties
% 2.05/0.99  
% 2.05/0.99  clauses:                                16
% 2.05/0.99  conjectures:                            2
% 2.05/0.99  epr:                                    0
% 2.05/0.99  horn:                                   12
% 2.05/0.99  ground:                                 14
% 2.05/0.99  unary:                                  7
% 2.05/0.99  binary:                                 1
% 2.05/0.99  lits:                                   57
% 2.05/0.99  lits_eq:                                21
% 2.05/0.99  fd_pure:                                0
% 2.05/0.99  fd_pseudo:                              0
% 2.05/0.99  fd_cond:                                0
% 2.05/0.99  fd_pseudo_cond:                         0
% 2.05/0.99  ac_symbols:                             0
% 2.05/0.99  
% 2.05/0.99  ------ Propositional Solver
% 2.05/0.99  
% 2.05/0.99  prop_solver_calls:                      21
% 2.05/0.99  prop_fast_solver_calls:                 1979
% 2.05/0.99  smt_solver_calls:                       0
% 2.05/0.99  smt_fast_solver_calls:                  0
% 2.05/0.99  prop_num_of_clauses:                    460
% 2.05/0.99  prop_preprocess_simplified:             2264
% 2.05/0.99  prop_fo_subsumed:                       95
% 2.05/0.99  prop_solver_time:                       0.
% 2.05/0.99  smt_solver_time:                        0.
% 2.05/0.99  smt_fast_solver_time:                   0.
% 2.05/0.99  prop_fast_solver_time:                  0.
% 2.05/0.99  prop_unsat_core_time:                   0.
% 2.05/0.99  
% 2.05/0.99  ------ QBF
% 2.05/0.99  
% 2.05/0.99  qbf_q_res:                              0
% 2.05/0.99  qbf_num_tautologies:                    0
% 2.05/0.99  qbf_prep_cycles:                        0
% 2.05/0.99  
% 2.05/0.99  ------ BMC1
% 2.05/0.99  
% 2.05/0.99  bmc1_current_bound:                     -1
% 2.05/0.99  bmc1_last_solved_bound:                 -1
% 2.05/0.99  bmc1_unsat_core_size:                   -1
% 2.05/0.99  bmc1_unsat_core_parents_size:           -1
% 2.05/0.99  bmc1_merge_next_fun:                    0
% 2.05/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.05/0.99  
% 2.05/0.99  ------ Instantiation
% 2.05/0.99  
% 2.05/0.99  inst_num_of_clauses:                    29
% 2.05/0.99  inst_num_in_passive:                    0
% 2.05/0.99  inst_num_in_active:                     0
% 2.05/0.99  inst_num_in_unprocessed:                29
% 2.05/0.99  inst_num_of_loops:                      0
% 2.05/0.99  inst_num_of_learning_restarts:          0
% 2.05/0.99  inst_num_moves_active_passive:          0
% 2.05/0.99  inst_lit_activity:                      0
% 2.05/0.99  inst_lit_activity_moves:                0
% 2.05/0.99  inst_num_tautologies:                   0
% 2.05/0.99  inst_num_prop_implied:                  0
% 2.05/0.99  inst_num_existing_simplified:           0
% 2.05/0.99  inst_num_eq_res_simplified:             0
% 2.05/0.99  inst_num_child_elim:                    0
% 2.05/0.99  inst_num_of_dismatching_blockings:      0
% 2.05/0.99  inst_num_of_non_proper_insts:           0
% 2.05/0.99  inst_num_of_duplicates:                 0
% 2.05/0.99  inst_inst_num_from_inst_to_res:         0
% 2.05/0.99  inst_dismatching_checking_time:         0.
% 2.05/0.99  
% 2.05/0.99  ------ Resolution
% 2.05/0.99  
% 2.05/0.99  res_num_of_clauses:                     0
% 2.05/0.99  res_num_in_passive:                     0
% 2.05/0.99  res_num_in_active:                      0
% 2.05/0.99  res_num_of_loops:                       104
% 2.05/0.99  res_forward_subset_subsumed:            5
% 2.05/0.99  res_backward_subset_subsumed:           0
% 2.05/0.99  res_forward_subsumed:                   12
% 2.05/0.99  res_backward_subsumed:                  12
% 2.05/0.99  res_forward_subsumption_resolution:     2
% 2.05/0.99  res_backward_subsumption_resolution:    0
% 2.05/0.99  res_clause_to_clause_subsumption:       375
% 2.05/0.99  res_orphan_elimination:                 0
% 2.05/0.99  res_tautology_del:                      7
% 2.05/0.99  res_num_eq_res_simplified:              0
% 2.05/0.99  res_num_sel_changes:                    0
% 2.05/0.99  res_moves_from_active_to_pass:          0
% 2.05/0.99  
% 2.05/0.99  ------ Superposition
% 2.05/0.99  
% 2.05/0.99  sup_time_total:                         0.
% 2.05/0.99  sup_time_generating:                    0.
% 2.05/0.99  sup_time_sim_full:                      0.
% 2.05/0.99  sup_time_sim_immed:                     0.
% 2.05/0.99  
% 2.05/0.99  sup_num_of_clauses:                     0
% 2.05/0.99  sup_num_in_active:                      0
% 2.05/0.99  sup_num_in_passive:                     0
% 2.05/0.99  sup_num_of_loops:                       0
% 2.05/0.99  sup_fw_superposition:                   0
% 2.05/0.99  sup_bw_superposition:                   0
% 2.05/0.99  sup_immediate_simplified:               0
% 2.05/0.99  sup_given_eliminated:                   0
% 2.05/0.99  comparisons_done:                       0
% 2.05/0.99  comparisons_avoided:                    0
% 2.05/0.99  
% 2.05/0.99  ------ Simplifications
% 2.05/0.99  
% 2.05/0.99  
% 2.05/0.99  sim_fw_subset_subsumed:                 0
% 2.05/0.99  sim_bw_subset_subsumed:                 0
% 2.05/0.99  sim_fw_subsumed:                        1
% 2.05/0.99  sim_bw_subsumed:                        1
% 2.05/0.99  sim_fw_subsumption_res:                 14
% 2.05/0.99  sim_bw_subsumption_res:                 0
% 2.05/0.99  sim_tautology_del:                      0
% 2.05/0.99  sim_eq_tautology_del:                   0
% 2.05/0.99  sim_eq_res_simp:                        4
% 2.05/0.99  sim_fw_demodulated:                     1
% 2.05/0.99  sim_bw_demodulated:                     0
% 2.05/0.99  sim_light_normalised:                   10
% 2.05/0.99  sim_joinable_taut:                      0
% 2.05/0.99  sim_joinable_simp:                      0
% 2.05/0.99  sim_ac_normalised:                      0
% 2.05/0.99  sim_smt_subsumption:                    0
% 2.05/0.99  
%------------------------------------------------------------------------------
