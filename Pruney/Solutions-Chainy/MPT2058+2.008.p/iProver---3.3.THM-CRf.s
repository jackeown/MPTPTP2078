%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:15 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  272 (2711 expanded)
%              Number of clauses        :  171 ( 656 expanded)
%              Number of leaves         :   24 ( 708 expanded)
%              Depth                    :   31
%              Number of atoms          : 1565 (22169 expanded)
%              Number of equality atoms :  288 ( 985 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_waybel_7(X0,X1,X2)
            | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & ( r1_waybel_7(X0,X1,X2)
            | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_waybel_7(X0,X1,sK4)
          | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK4) )
        & ( r1_waybel_7(X0,X1,sK4)
          | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK4) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
            ( ( ~ r1_waybel_7(X0,sK3,X2)
              | ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK3),X2) )
            & ( r1_waybel_7(X0,sK3,X2)
              | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK3),X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
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
              ( ( ~ r1_waybel_7(sK2,X1,X2)
                | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1),X2) )
              & ( r1_waybel_7(sK2,X1,X2)
                | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1),X2) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ r1_waybel_7(sK2,sK3,sK4)
      | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) )
    & ( r1_waybel_7(sK2,sK3,sK4)
      | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))
    & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))
    & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))
    & ~ v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f57,f60,f59,f58])).

fof(f94,plain,(
    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f61])).

fof(f11,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f109,plain,(
    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f94,f77])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(pure_predicate_removal,[],[f13])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,(
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
    inference(definition_unfolding,[],[f81,f77,f77,f77])).

fof(f99,plain,
    ( ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f89,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f91,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f95,plain,(
    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f61])).

fof(f108,plain,(
    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(definition_unfolding,[],[f95,f77])).

fof(f92,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f69,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f61])).

fof(f107,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
    inference(definition_unfolding,[],[f96,f77])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK1(X0),X0)
        & ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK1(X0),X0)
        & ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f51])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f88,f77,f77,f77,f77])).

fof(f93,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f110,plain,(
    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(definition_unfolding,[],[f93,f77])).

fof(f98,plain,
    ( r1_waybel_7(sK2,sK3,sK4)
    | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).

fof(f63,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f15])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f104,plain,(
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
    inference(definition_unfolding,[],[f85,f77,f77,f77,f77])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f23,plain,(
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
    inference(pure_predicate_removal,[],[f20])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
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
    inference(definition_unfolding,[],[f83,f77,f77,f77])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,(
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
    inference(definition_unfolding,[],[f80,f77,f77,f77])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

cnf(c_31,negated_conjecture,
    ( v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_17,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_26,negated_conjecture,
    ( ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_274,plain,
    ( ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f87])).

cnf(c_35,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_737,plain,
    ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_738,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | r3_waybel_9(sK2,X0,X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_36,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_34,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_742,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | r3_waybel_9(sK2,X0,X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_738,c_36,c_34])).

cnf(c_1181,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != X0
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_274,c_742])).

cnf(c_1182,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(unflattening,[status(thm)],[c_1181])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1184,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1182,c_28])).

cnf(c_1185,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(renaming,[status(thm)],[c_1184])).

cnf(c_1221,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(X2,X1,X0)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1185])).

cnf(c_1222,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1221])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_104,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1226,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1222,c_36,c_34,c_104])).

cnf(c_30,negated_conjecture,
    ( v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1805,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1226,c_30])).

cnf(c_1806,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1805])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1810,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1806,c_33])).

cnf(c_1811,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1810])).

cnf(c_2154,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1811])).

cnf(c_2710,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2154])).

cnf(c_3190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_2710])).

cnf(c_3551,plain,
    ( k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3190])).

cnf(c_7,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | X1 != X2
    | k2_pre_topc(X1,X0) = X0
    | k2_struct_0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_589,plain,
    ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_588])).

cnf(c_5,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_593,plain,
    ( ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_589,c_6,c_5])).

cnf(c_696,plain,
    ( ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_593,c_35])).

cnf(c_697,plain,
    ( ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_696])).

cnf(c_107,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_591,plain,
    ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_699,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_697,c_35,c_34,c_104,c_107,c_591])).

cnf(c_13,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_16,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(resolution,[status(thm)],[c_13,c_16])).

cnf(c_821,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_660,c_34])).

cnf(c_822,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
    | k2_pre_topc(sK2,X0) != k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_821])).

cnf(c_3558,plain,
    ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
    | k2_pre_topc(sK2,X0) != k2_struct_0(sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_4260,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) = u1_struct_0(sK2)
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_699,c_3558])).

cnf(c_4271,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4260,c_699])).

cnf(c_39,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_103,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_105,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_106,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_108,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_struct_0(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_4277,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4271,c_39,c_105,c_108])).

cnf(c_4552,plain,
    ( k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3551,c_4277])).

cnf(c_4562,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4552])).

cnf(c_4629,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4562])).

cnf(c_37,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_38,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_94,plain,
    ( v2_struct_0(X0) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(sK1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_96,plain,
    ( v2_struct_0(sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(sK1(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_3191,plain,
    ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ r1_waybel_7(sK2,sK3,sK4)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2710])).

cnf(c_3550,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4) != iProver_top
    | r1_waybel_7(sK2,sK3,sK4) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3191])).

cnf(c_25,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_32,negated_conjecture,
    ( v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_536,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_32])).

cnf(c_537,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK3)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_541,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_537,c_33])).

cnf(c_542,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(renaming,[status(thm)],[c_541])).

cnf(c_814,plain,
    ( l1_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_34])).

cnf(c_815,plain,
    ( l1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_814])).

cnf(c_1319,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_542,c_815])).

cnf(c_1320,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
    | v2_struct_0(sK2)
    | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(unflattening,[status(thm)],[c_1319])).

cnf(c_1322,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1320,c_36,c_31,c_30,c_29])).

cnf(c_2719,plain,
    ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3 ),
    inference(equality_resolution_simp,[status(thm)],[c_1322])).

cnf(c_3665,plain,
    ( r1_waybel_7(sK2,sK3,sK4) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3550,c_2719])).

cnf(c_27,negated_conjecture,
    ( r1_waybel_7(sK2,sK3,sK4)
    | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_276,plain,
    ( r1_waybel_7(sK2,sK3,sK4)
    | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f86])).

cnf(c_704,plain,
    ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r3_waybel_9(X0,X1,X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_705,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ r3_waybel_9(sK2,X0,X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_709,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | ~ r3_waybel_9(sK2,X0,X1)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_705,c_36,c_34])).

cnf(c_1155,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != X0
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_276,c_709])).

cnf(c_1156,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(unflattening,[status(thm)],[c_1155])).

cnf(c_1158,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | r1_waybel_7(sK2,sK3,sK4)
    | r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1156,c_28])).

cnf(c_1159,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
    inference(renaming,[status(thm)],[c_1158])).

cnf(c_1269,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(X2)
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(X2,X1,X0)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1159])).

cnf(c_1270,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1269])).

cnf(c_1274,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1270,c_36,c_34,c_104])).

cnf(c_1760,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1274,c_30])).

cnf(c_1761,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1760])).

cnf(c_1765,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | r1_waybel_7(sK2,sK3,sK4)
    | r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1761,c_33])).

cnf(c_1766,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1765])).

cnf(c_2192,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1766])).

cnf(c_2706,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v1_xboole_0(X0)
    | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2192])).

cnf(c_3192,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
    | r1_waybel_7(sK2,sK3,sK4)
    | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_2706])).

cnf(c_3552,plain,
    ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4) = iProver_top
    | r1_waybel_7(sK2,sK3,sK4) = iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3192])).

cnf(c_3642,plain,
    ( r1_waybel_7(sK2,sK3,sK4) = iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3552,c_2719])).

cnf(c_3671,plain,
    ( v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3665,c_3642])).

cnf(c_10,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_770,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_35])).

cnf(c_771,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_92,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_773,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_771,c_36,c_35,c_34,c_92])).

cnf(c_3560,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_4284,plain,
    ( m1_subset_1(sK1(sK2),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4277,c_3560])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_3561,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_4359,plain,
    ( v1_xboole_0(sK1(sK2)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4284,c_3561])).

cnf(c_21,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_497,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_498,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_497])).

cnf(c_502,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_498,c_33])).

cnf(c_503,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_502])).

cnf(c_1403,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK3))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_503,c_815])).

cnf(c_1404,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1403])).

cnf(c_1408,plain,
    ( v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1404,c_36])).

cnf(c_1409,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1408])).

cnf(c_1850,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_1409])).

cnf(c_2128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1850])).

cnf(c_2714,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2128])).

cnf(c_3549,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2714])).

cnf(c_4399,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,X0,sK3)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3549,c_4277])).

cnf(c_4409,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4399])).

cnf(c_19,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1337,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_815])).

cnf(c_1338,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_orders_2(k3_yellow19(sK2,X1,X0))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1337])).

cnf(c_1342,plain,
    ( v4_orders_2(k3_yellow19(sK2,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1338,c_36])).

cnf(c_1343,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_orders_2(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1342])).

cnf(c_1730,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_orders_2(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1343,c_30])).

cnf(c_1731,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1730])).

cnf(c_1735,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1731,c_33])).

cnf(c_1736,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1735])).

cnf(c_2230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1736])).

cnf(c_2702,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2230])).

cnf(c_3554,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,X0,sK3)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2702])).

cnf(c_4412,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,X0,sK3)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3554,c_4277])).

cnf(c_4421,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4412])).

cnf(c_18,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1370,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_815])).

cnf(c_1371,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
    | v2_struct_0(sK2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_1370])).

cnf(c_1375,plain,
    ( ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1371,c_36])).

cnf(c_1376,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_1375])).

cnf(c_1700,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1376,c_30])).

cnf(c_1701,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1700])).

cnf(c_1705,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1701,c_33])).

cnf(c_1706,plain,
    ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1705])).

cnf(c_2253,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_1706])).

cnf(c_2698,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2253])).

cnf(c_3555,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,X0,sK3)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2698])).

cnf(c_4462,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,X0,sK3)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3555,c_4277])).

cnf(c_4471,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4462])).

cnf(c_4570,plain,
    ( v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4471,c_37,c_38,c_39,c_44,c_96,c_4359])).

cnf(c_4571,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4570])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3566,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3581,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3566,c_2])).

cnf(c_4576,plain,
    ( v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4571,c_3581])).

cnf(c_3194,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4617,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) = k3_lattice3(k1_lattice3(k2_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3194])).

cnf(c_4631,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4629,c_37,c_38,c_39,c_44,c_96,c_3671,c_4359,c_4409,c_4421,c_4576,c_4617])).

cnf(c_4636,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4631,c_3581])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.22/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/0.98  
% 2.22/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.22/0.98  
% 2.22/0.98  ------  iProver source info
% 2.22/0.98  
% 2.22/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.22/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.22/0.98  git: non_committed_changes: false
% 2.22/0.98  git: last_make_outside_of_git: false
% 2.22/0.98  
% 2.22/0.98  ------ 
% 2.22/0.98  
% 2.22/0.98  ------ Input Options
% 2.22/0.98  
% 2.22/0.98  --out_options                           all
% 2.22/0.98  --tptp_safe_out                         true
% 2.22/0.98  --problem_path                          ""
% 2.22/0.98  --include_path                          ""
% 2.22/0.98  --clausifier                            res/vclausify_rel
% 2.22/0.98  --clausifier_options                    --mode clausify
% 2.22/0.98  --stdin                                 false
% 2.22/0.98  --stats_out                             all
% 2.22/0.98  
% 2.22/0.98  ------ General Options
% 2.22/0.98  
% 2.22/0.98  --fof                                   false
% 2.22/0.98  --time_out_real                         305.
% 2.22/0.98  --time_out_virtual                      -1.
% 2.22/0.98  --symbol_type_check                     false
% 2.22/0.98  --clausify_out                          false
% 2.22/0.98  --sig_cnt_out                           false
% 2.22/0.98  --trig_cnt_out                          false
% 2.22/0.98  --trig_cnt_out_tolerance                1.
% 2.22/0.98  --trig_cnt_out_sk_spl                   false
% 2.22/0.98  --abstr_cl_out                          false
% 2.22/0.98  
% 2.22/0.98  ------ Global Options
% 2.22/0.98  
% 2.22/0.98  --schedule                              default
% 2.22/0.98  --add_important_lit                     false
% 2.22/0.98  --prop_solver_per_cl                    1000
% 2.22/0.98  --min_unsat_core                        false
% 2.22/0.98  --soft_assumptions                      false
% 2.22/0.98  --soft_lemma_size                       3
% 2.22/0.98  --prop_impl_unit_size                   0
% 2.22/0.98  --prop_impl_unit                        []
% 2.22/0.98  --share_sel_clauses                     true
% 2.22/0.98  --reset_solvers                         false
% 2.22/0.98  --bc_imp_inh                            [conj_cone]
% 2.22/0.98  --conj_cone_tolerance                   3.
% 2.22/0.98  --extra_neg_conj                        none
% 2.22/0.98  --large_theory_mode                     true
% 2.22/0.98  --prolific_symb_bound                   200
% 2.22/0.98  --lt_threshold                          2000
% 2.22/0.98  --clause_weak_htbl                      true
% 2.22/0.98  --gc_record_bc_elim                     false
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing Options
% 2.22/0.98  
% 2.22/0.98  --preprocessing_flag                    true
% 2.22/0.98  --time_out_prep_mult                    0.1
% 2.22/0.98  --splitting_mode                        input
% 2.22/0.98  --splitting_grd                         true
% 2.22/0.98  --splitting_cvd                         false
% 2.22/0.98  --splitting_cvd_svl                     false
% 2.22/0.98  --splitting_nvd                         32
% 2.22/0.98  --sub_typing                            true
% 2.22/0.98  --prep_gs_sim                           true
% 2.22/0.98  --prep_unflatten                        true
% 2.22/0.98  --prep_res_sim                          true
% 2.22/0.98  --prep_upred                            true
% 2.22/0.98  --prep_sem_filter                       exhaustive
% 2.22/0.98  --prep_sem_filter_out                   false
% 2.22/0.98  --pred_elim                             true
% 2.22/0.98  --res_sim_input                         true
% 2.22/0.98  --eq_ax_congr_red                       true
% 2.22/0.98  --pure_diseq_elim                       true
% 2.22/0.98  --brand_transform                       false
% 2.22/0.98  --non_eq_to_eq                          false
% 2.22/0.98  --prep_def_merge                        true
% 2.22/0.98  --prep_def_merge_prop_impl              false
% 2.22/0.98  --prep_def_merge_mbd                    true
% 2.22/0.98  --prep_def_merge_tr_red                 false
% 2.22/0.98  --prep_def_merge_tr_cl                  false
% 2.22/0.98  --smt_preprocessing                     true
% 2.22/0.98  --smt_ac_axioms                         fast
% 2.22/0.98  --preprocessed_out                      false
% 2.22/0.98  --preprocessed_stats                    false
% 2.22/0.98  
% 2.22/0.98  ------ Abstraction refinement Options
% 2.22/0.98  
% 2.22/0.98  --abstr_ref                             []
% 2.22/0.98  --abstr_ref_prep                        false
% 2.22/0.98  --abstr_ref_until_sat                   false
% 2.22/0.98  --abstr_ref_sig_restrict                funpre
% 2.22/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/0.98  --abstr_ref_under                       []
% 2.22/0.98  
% 2.22/0.98  ------ SAT Options
% 2.22/0.98  
% 2.22/0.98  --sat_mode                              false
% 2.22/0.98  --sat_fm_restart_options                ""
% 2.22/0.98  --sat_gr_def                            false
% 2.22/0.98  --sat_epr_types                         true
% 2.22/0.98  --sat_non_cyclic_types                  false
% 2.22/0.98  --sat_finite_models                     false
% 2.22/0.98  --sat_fm_lemmas                         false
% 2.22/0.98  --sat_fm_prep                           false
% 2.22/0.98  --sat_fm_uc_incr                        true
% 2.22/0.98  --sat_out_model                         small
% 2.22/0.98  --sat_out_clauses                       false
% 2.22/0.98  
% 2.22/0.98  ------ QBF Options
% 2.22/0.98  
% 2.22/0.98  --qbf_mode                              false
% 2.22/0.98  --qbf_elim_univ                         false
% 2.22/0.98  --qbf_dom_inst                          none
% 2.22/0.98  --qbf_dom_pre_inst                      false
% 2.22/0.98  --qbf_sk_in                             false
% 2.22/0.98  --qbf_pred_elim                         true
% 2.22/0.98  --qbf_split                             512
% 2.22/0.98  
% 2.22/0.98  ------ BMC1 Options
% 2.22/0.98  
% 2.22/0.98  --bmc1_incremental                      false
% 2.22/0.98  --bmc1_axioms                           reachable_all
% 2.22/0.98  --bmc1_min_bound                        0
% 2.22/0.98  --bmc1_max_bound                        -1
% 2.22/0.98  --bmc1_max_bound_default                -1
% 2.22/0.98  --bmc1_symbol_reachability              true
% 2.22/0.98  --bmc1_property_lemmas                  false
% 2.22/0.98  --bmc1_k_induction                      false
% 2.22/0.98  --bmc1_non_equiv_states                 false
% 2.22/0.98  --bmc1_deadlock                         false
% 2.22/0.98  --bmc1_ucm                              false
% 2.22/0.98  --bmc1_add_unsat_core                   none
% 2.22/0.98  --bmc1_unsat_core_children              false
% 2.22/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/0.98  --bmc1_out_stat                         full
% 2.22/0.98  --bmc1_ground_init                      false
% 2.22/0.98  --bmc1_pre_inst_next_state              false
% 2.22/0.98  --bmc1_pre_inst_state                   false
% 2.22/0.98  --bmc1_pre_inst_reach_state             false
% 2.22/0.98  --bmc1_out_unsat_core                   false
% 2.22/0.98  --bmc1_aig_witness_out                  false
% 2.22/0.98  --bmc1_verbose                          false
% 2.22/0.98  --bmc1_dump_clauses_tptp                false
% 2.22/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.22/0.98  --bmc1_dump_file                        -
% 2.22/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.22/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.22/0.98  --bmc1_ucm_extend_mode                  1
% 2.22/0.98  --bmc1_ucm_init_mode                    2
% 2.22/0.98  --bmc1_ucm_cone_mode                    none
% 2.22/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.22/0.98  --bmc1_ucm_relax_model                  4
% 2.22/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.22/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/0.98  --bmc1_ucm_layered_model                none
% 2.22/0.98  --bmc1_ucm_max_lemma_size               10
% 2.22/0.98  
% 2.22/0.98  ------ AIG Options
% 2.22/0.98  
% 2.22/0.98  --aig_mode                              false
% 2.22/0.98  
% 2.22/0.98  ------ Instantiation Options
% 2.22/0.98  
% 2.22/0.98  --instantiation_flag                    true
% 2.22/0.98  --inst_sos_flag                         false
% 2.22/0.98  --inst_sos_phase                        true
% 2.22/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/0.98  --inst_lit_sel_side                     num_symb
% 2.22/0.98  --inst_solver_per_active                1400
% 2.22/0.98  --inst_solver_calls_frac                1.
% 2.22/0.98  --inst_passive_queue_type               priority_queues
% 2.22/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/0.98  --inst_passive_queues_freq              [25;2]
% 2.22/0.98  --inst_dismatching                      true
% 2.22/0.98  --inst_eager_unprocessed_to_passive     true
% 2.22/0.98  --inst_prop_sim_given                   true
% 2.22/0.98  --inst_prop_sim_new                     false
% 2.22/0.98  --inst_subs_new                         false
% 2.22/0.98  --inst_eq_res_simp                      false
% 2.22/0.98  --inst_subs_given                       false
% 2.22/0.98  --inst_orphan_elimination               true
% 2.22/0.98  --inst_learning_loop_flag               true
% 2.22/0.98  --inst_learning_start                   3000
% 2.22/0.98  --inst_learning_factor                  2
% 2.22/0.98  --inst_start_prop_sim_after_learn       3
% 2.22/0.98  --inst_sel_renew                        solver
% 2.22/0.98  --inst_lit_activity_flag                true
% 2.22/0.98  --inst_restr_to_given                   false
% 2.22/0.98  --inst_activity_threshold               500
% 2.22/0.98  --inst_out_proof                        true
% 2.22/0.98  
% 2.22/0.98  ------ Resolution Options
% 2.22/0.98  
% 2.22/0.98  --resolution_flag                       true
% 2.22/0.98  --res_lit_sel                           adaptive
% 2.22/0.98  --res_lit_sel_side                      none
% 2.22/0.98  --res_ordering                          kbo
% 2.22/0.98  --res_to_prop_solver                    active
% 2.22/0.98  --res_prop_simpl_new                    false
% 2.22/0.98  --res_prop_simpl_given                  true
% 2.22/0.98  --res_passive_queue_type                priority_queues
% 2.22/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/0.98  --res_passive_queues_freq               [15;5]
% 2.22/0.98  --res_forward_subs                      full
% 2.22/0.98  --res_backward_subs                     full
% 2.22/0.98  --res_forward_subs_resolution           true
% 2.22/0.98  --res_backward_subs_resolution          true
% 2.22/0.98  --res_orphan_elimination                true
% 2.22/0.98  --res_time_limit                        2.
% 2.22/0.98  --res_out_proof                         true
% 2.22/0.98  
% 2.22/0.98  ------ Superposition Options
% 2.22/0.98  
% 2.22/0.98  --superposition_flag                    true
% 2.22/0.98  --sup_passive_queue_type                priority_queues
% 2.22/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.22/0.98  --demod_completeness_check              fast
% 2.22/0.98  --demod_use_ground                      true
% 2.22/0.98  --sup_to_prop_solver                    passive
% 2.22/0.98  --sup_prop_simpl_new                    true
% 2.22/0.98  --sup_prop_simpl_given                  true
% 2.22/0.98  --sup_fun_splitting                     false
% 2.22/0.98  --sup_smt_interval                      50000
% 2.22/0.98  
% 2.22/0.98  ------ Superposition Simplification Setup
% 2.22/0.98  
% 2.22/0.98  --sup_indices_passive                   []
% 2.22/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_full_bw                           [BwDemod]
% 2.22/0.98  --sup_immed_triv                        [TrivRules]
% 2.22/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_immed_bw_main                     []
% 2.22/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.98  
% 2.22/0.98  ------ Combination Options
% 2.22/0.98  
% 2.22/0.98  --comb_res_mult                         3
% 2.22/0.98  --comb_sup_mult                         2
% 2.22/0.98  --comb_inst_mult                        10
% 2.22/0.98  
% 2.22/0.98  ------ Debug Options
% 2.22/0.98  
% 2.22/0.98  --dbg_backtrace                         false
% 2.22/0.98  --dbg_dump_prop_clauses                 false
% 2.22/0.98  --dbg_dump_prop_clauses_file            -
% 2.22/0.98  --dbg_out_stat                          false
% 2.22/0.98  ------ Parsing...
% 2.22/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 10 0s  sf_e  pe_s  pe_e 
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.22/0.98  ------ Proving...
% 2.22/0.98  ------ Problem Properties 
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  clauses                                 22
% 2.22/0.98  conjectures                             4
% 2.22/0.98  EPR                                     2
% 2.22/0.98  Horn                                    18
% 2.22/0.98  unary                                   12
% 2.22/0.98  binary                                  0
% 2.22/0.98  lits                                    61
% 2.22/0.98  lits eq                                 16
% 2.22/0.98  fd_pure                                 0
% 2.22/0.98  fd_pseudo                               0
% 2.22/0.98  fd_cond                                 0
% 2.22/0.98  fd_pseudo_cond                          0
% 2.22/0.98  AC symbols                              0
% 2.22/0.98  
% 2.22/0.98  ------ Schedule dynamic 5 is on 
% 2.22/0.98  
% 2.22/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  ------ 
% 2.22/0.98  Current options:
% 2.22/0.98  ------ 
% 2.22/0.98  
% 2.22/0.98  ------ Input Options
% 2.22/0.98  
% 2.22/0.98  --out_options                           all
% 2.22/0.98  --tptp_safe_out                         true
% 2.22/0.98  --problem_path                          ""
% 2.22/0.98  --include_path                          ""
% 2.22/0.98  --clausifier                            res/vclausify_rel
% 2.22/0.98  --clausifier_options                    --mode clausify
% 2.22/0.98  --stdin                                 false
% 2.22/0.98  --stats_out                             all
% 2.22/0.98  
% 2.22/0.98  ------ General Options
% 2.22/0.98  
% 2.22/0.98  --fof                                   false
% 2.22/0.98  --time_out_real                         305.
% 2.22/0.98  --time_out_virtual                      -1.
% 2.22/0.98  --symbol_type_check                     false
% 2.22/0.98  --clausify_out                          false
% 2.22/0.98  --sig_cnt_out                           false
% 2.22/0.98  --trig_cnt_out                          false
% 2.22/0.98  --trig_cnt_out_tolerance                1.
% 2.22/0.98  --trig_cnt_out_sk_spl                   false
% 2.22/0.98  --abstr_cl_out                          false
% 2.22/0.98  
% 2.22/0.98  ------ Global Options
% 2.22/0.98  
% 2.22/0.98  --schedule                              default
% 2.22/0.98  --add_important_lit                     false
% 2.22/0.98  --prop_solver_per_cl                    1000
% 2.22/0.98  --min_unsat_core                        false
% 2.22/0.98  --soft_assumptions                      false
% 2.22/0.98  --soft_lemma_size                       3
% 2.22/0.98  --prop_impl_unit_size                   0
% 2.22/0.98  --prop_impl_unit                        []
% 2.22/0.98  --share_sel_clauses                     true
% 2.22/0.98  --reset_solvers                         false
% 2.22/0.98  --bc_imp_inh                            [conj_cone]
% 2.22/0.98  --conj_cone_tolerance                   3.
% 2.22/0.98  --extra_neg_conj                        none
% 2.22/0.98  --large_theory_mode                     true
% 2.22/0.98  --prolific_symb_bound                   200
% 2.22/0.98  --lt_threshold                          2000
% 2.22/0.98  --clause_weak_htbl                      true
% 2.22/0.98  --gc_record_bc_elim                     false
% 2.22/0.98  
% 2.22/0.98  ------ Preprocessing Options
% 2.22/0.98  
% 2.22/0.98  --preprocessing_flag                    true
% 2.22/0.98  --time_out_prep_mult                    0.1
% 2.22/0.98  --splitting_mode                        input
% 2.22/0.98  --splitting_grd                         true
% 2.22/0.98  --splitting_cvd                         false
% 2.22/0.98  --splitting_cvd_svl                     false
% 2.22/0.98  --splitting_nvd                         32
% 2.22/0.98  --sub_typing                            true
% 2.22/0.98  --prep_gs_sim                           true
% 2.22/0.98  --prep_unflatten                        true
% 2.22/0.98  --prep_res_sim                          true
% 2.22/0.98  --prep_upred                            true
% 2.22/0.98  --prep_sem_filter                       exhaustive
% 2.22/0.98  --prep_sem_filter_out                   false
% 2.22/0.98  --pred_elim                             true
% 2.22/0.98  --res_sim_input                         true
% 2.22/0.98  --eq_ax_congr_red                       true
% 2.22/0.98  --pure_diseq_elim                       true
% 2.22/0.98  --brand_transform                       false
% 2.22/0.98  --non_eq_to_eq                          false
% 2.22/0.98  --prep_def_merge                        true
% 2.22/0.98  --prep_def_merge_prop_impl              false
% 2.22/0.98  --prep_def_merge_mbd                    true
% 2.22/0.98  --prep_def_merge_tr_red                 false
% 2.22/0.98  --prep_def_merge_tr_cl                  false
% 2.22/0.98  --smt_preprocessing                     true
% 2.22/0.98  --smt_ac_axioms                         fast
% 2.22/0.98  --preprocessed_out                      false
% 2.22/0.98  --preprocessed_stats                    false
% 2.22/0.98  
% 2.22/0.98  ------ Abstraction refinement Options
% 2.22/0.98  
% 2.22/0.98  --abstr_ref                             []
% 2.22/0.98  --abstr_ref_prep                        false
% 2.22/0.98  --abstr_ref_until_sat                   false
% 2.22/0.98  --abstr_ref_sig_restrict                funpre
% 2.22/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.22/0.98  --abstr_ref_under                       []
% 2.22/0.98  
% 2.22/0.98  ------ SAT Options
% 2.22/0.98  
% 2.22/0.98  --sat_mode                              false
% 2.22/0.98  --sat_fm_restart_options                ""
% 2.22/0.98  --sat_gr_def                            false
% 2.22/0.98  --sat_epr_types                         true
% 2.22/0.98  --sat_non_cyclic_types                  false
% 2.22/0.98  --sat_finite_models                     false
% 2.22/0.98  --sat_fm_lemmas                         false
% 2.22/0.98  --sat_fm_prep                           false
% 2.22/0.98  --sat_fm_uc_incr                        true
% 2.22/0.98  --sat_out_model                         small
% 2.22/0.98  --sat_out_clauses                       false
% 2.22/0.98  
% 2.22/0.98  ------ QBF Options
% 2.22/0.98  
% 2.22/0.98  --qbf_mode                              false
% 2.22/0.98  --qbf_elim_univ                         false
% 2.22/0.98  --qbf_dom_inst                          none
% 2.22/0.98  --qbf_dom_pre_inst                      false
% 2.22/0.98  --qbf_sk_in                             false
% 2.22/0.98  --qbf_pred_elim                         true
% 2.22/0.98  --qbf_split                             512
% 2.22/0.98  
% 2.22/0.98  ------ BMC1 Options
% 2.22/0.98  
% 2.22/0.98  --bmc1_incremental                      false
% 2.22/0.98  --bmc1_axioms                           reachable_all
% 2.22/0.98  --bmc1_min_bound                        0
% 2.22/0.98  --bmc1_max_bound                        -1
% 2.22/0.98  --bmc1_max_bound_default                -1
% 2.22/0.98  --bmc1_symbol_reachability              true
% 2.22/0.98  --bmc1_property_lemmas                  false
% 2.22/0.98  --bmc1_k_induction                      false
% 2.22/0.98  --bmc1_non_equiv_states                 false
% 2.22/0.98  --bmc1_deadlock                         false
% 2.22/0.98  --bmc1_ucm                              false
% 2.22/0.98  --bmc1_add_unsat_core                   none
% 2.22/0.98  --bmc1_unsat_core_children              false
% 2.22/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.22/0.98  --bmc1_out_stat                         full
% 2.22/0.98  --bmc1_ground_init                      false
% 2.22/0.98  --bmc1_pre_inst_next_state              false
% 2.22/0.98  --bmc1_pre_inst_state                   false
% 2.22/0.98  --bmc1_pre_inst_reach_state             false
% 2.22/0.98  --bmc1_out_unsat_core                   false
% 2.22/0.98  --bmc1_aig_witness_out                  false
% 2.22/0.98  --bmc1_verbose                          false
% 2.22/0.98  --bmc1_dump_clauses_tptp                false
% 2.22/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.22/0.98  --bmc1_dump_file                        -
% 2.22/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.22/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.22/0.98  --bmc1_ucm_extend_mode                  1
% 2.22/0.98  --bmc1_ucm_init_mode                    2
% 2.22/0.98  --bmc1_ucm_cone_mode                    none
% 2.22/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.22/0.98  --bmc1_ucm_relax_model                  4
% 2.22/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.22/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.22/0.98  --bmc1_ucm_layered_model                none
% 2.22/0.98  --bmc1_ucm_max_lemma_size               10
% 2.22/0.98  
% 2.22/0.98  ------ AIG Options
% 2.22/0.98  
% 2.22/0.98  --aig_mode                              false
% 2.22/0.98  
% 2.22/0.98  ------ Instantiation Options
% 2.22/0.98  
% 2.22/0.98  --instantiation_flag                    true
% 2.22/0.98  --inst_sos_flag                         false
% 2.22/0.98  --inst_sos_phase                        true
% 2.22/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.22/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.22/0.98  --inst_lit_sel_side                     none
% 2.22/0.98  --inst_solver_per_active                1400
% 2.22/0.98  --inst_solver_calls_frac                1.
% 2.22/0.98  --inst_passive_queue_type               priority_queues
% 2.22/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.22/0.98  --inst_passive_queues_freq              [25;2]
% 2.22/0.98  --inst_dismatching                      true
% 2.22/0.98  --inst_eager_unprocessed_to_passive     true
% 2.22/0.98  --inst_prop_sim_given                   true
% 2.22/0.98  --inst_prop_sim_new                     false
% 2.22/0.98  --inst_subs_new                         false
% 2.22/0.98  --inst_eq_res_simp                      false
% 2.22/0.98  --inst_subs_given                       false
% 2.22/0.98  --inst_orphan_elimination               true
% 2.22/0.98  --inst_learning_loop_flag               true
% 2.22/0.98  --inst_learning_start                   3000
% 2.22/0.98  --inst_learning_factor                  2
% 2.22/0.98  --inst_start_prop_sim_after_learn       3
% 2.22/0.98  --inst_sel_renew                        solver
% 2.22/0.98  --inst_lit_activity_flag                true
% 2.22/0.98  --inst_restr_to_given                   false
% 2.22/0.98  --inst_activity_threshold               500
% 2.22/0.98  --inst_out_proof                        true
% 2.22/0.98  
% 2.22/0.98  ------ Resolution Options
% 2.22/0.98  
% 2.22/0.98  --resolution_flag                       false
% 2.22/0.98  --res_lit_sel                           adaptive
% 2.22/0.98  --res_lit_sel_side                      none
% 2.22/0.98  --res_ordering                          kbo
% 2.22/0.98  --res_to_prop_solver                    active
% 2.22/0.98  --res_prop_simpl_new                    false
% 2.22/0.98  --res_prop_simpl_given                  true
% 2.22/0.98  --res_passive_queue_type                priority_queues
% 2.22/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.22/0.98  --res_passive_queues_freq               [15;5]
% 2.22/0.98  --res_forward_subs                      full
% 2.22/0.98  --res_backward_subs                     full
% 2.22/0.98  --res_forward_subs_resolution           true
% 2.22/0.98  --res_backward_subs_resolution          true
% 2.22/0.98  --res_orphan_elimination                true
% 2.22/0.98  --res_time_limit                        2.
% 2.22/0.98  --res_out_proof                         true
% 2.22/0.98  
% 2.22/0.98  ------ Superposition Options
% 2.22/0.98  
% 2.22/0.98  --superposition_flag                    true
% 2.22/0.98  --sup_passive_queue_type                priority_queues
% 2.22/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.22/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.22/0.98  --demod_completeness_check              fast
% 2.22/0.98  --demod_use_ground                      true
% 2.22/0.98  --sup_to_prop_solver                    passive
% 2.22/0.98  --sup_prop_simpl_new                    true
% 2.22/0.98  --sup_prop_simpl_given                  true
% 2.22/0.98  --sup_fun_splitting                     false
% 2.22/0.98  --sup_smt_interval                      50000
% 2.22/0.98  
% 2.22/0.98  ------ Superposition Simplification Setup
% 2.22/0.98  
% 2.22/0.98  --sup_indices_passive                   []
% 2.22/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.22/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.22/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_full_bw                           [BwDemod]
% 2.22/0.98  --sup_immed_triv                        [TrivRules]
% 2.22/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.22/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_immed_bw_main                     []
% 2.22/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.22/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.22/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.22/0.98  
% 2.22/0.98  ------ Combination Options
% 2.22/0.98  
% 2.22/0.98  --comb_res_mult                         3
% 2.22/0.98  --comb_sup_mult                         2
% 2.22/0.98  --comb_inst_mult                        10
% 2.22/0.98  
% 2.22/0.98  ------ Debug Options
% 2.22/0.98  
% 2.22/0.98  --dbg_backtrace                         false
% 2.22/0.98  --dbg_dump_prop_clauses                 false
% 2.22/0.98  --dbg_dump_prop_clauses_file            -
% 2.22/0.98  --dbg_out_stat                          false
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  ------ Proving...
% 2.22/0.98  
% 2.22/0.98  
% 2.22/0.98  % SZS status Theorem for theBenchmark.p
% 2.22/0.98  
% 2.22/0.98   Resolution empty clause
% 2.22/0.98  
% 2.22/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.22/0.98  
% 2.22/0.98  fof(f18,conjecture,(
% 2.22/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f19,negated_conjecture,(
% 2.22/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.22/0.98    inference(negated_conjecture,[],[f18])).
% 2.22/0.98  
% 2.22/0.98  fof(f45,plain,(
% 2.22/0.98    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f19])).
% 2.22/0.98  
% 2.22/0.98  fof(f46,plain,(
% 2.22/0.98    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.98    inference(flattening,[],[f45])).
% 2.22/0.98  
% 2.22/0.98  fof(f56,plain,(
% 2.22/0.98    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.98    inference(nnf_transformation,[],[f46])).
% 2.22/0.98  
% 2.22/0.98  fof(f57,plain,(
% 2.22/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.22/0.98    inference(flattening,[],[f56])).
% 2.22/0.98  
% 2.22/0.98  fof(f60,plain,(
% 2.22/0.98    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK4) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK4)) & (r1_waybel_7(X0,X1,sK4) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK4)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.22/0.98    introduced(choice_axiom,[])).
% 2.22/0.98  
% 2.22/0.98  fof(f59,plain,(
% 2.22/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK3,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK3),X2)) & (r1_waybel_7(X0,sK3,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK3),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK3))) )),
% 2.22/0.98    introduced(choice_axiom,[])).
% 2.22/0.98  
% 2.22/0.98  fof(f58,plain,(
% 2.22/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK2,X1,X2) | ~r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1),X2)) & (r1_waybel_7(sK2,X1,X2) | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.22/0.98    introduced(choice_axiom,[])).
% 2.22/0.98  
% 2.22/0.98  fof(f61,plain,(
% 2.22/0.98    (((~r1_waybel_7(sK2,sK3,sK4) | ~r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4)) & (r1_waybel_7(sK2,sK3,sK4) | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4)) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))) & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2))) & v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))) & ~v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.22/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f57,f60,f59,f58])).
% 2.22/0.98  
% 2.22/0.98  fof(f94,plain,(
% 2.22/0.98    v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 2.22/0.98    inference(cnf_transformation,[],[f61])).
% 2.22/0.98  
% 2.22/0.98  fof(f11,axiom,(
% 2.22/0.98    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f77,plain,(
% 2.22/0.98    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.22/0.98    inference(cnf_transformation,[],[f11])).
% 2.22/0.98  
% 2.22/0.98  fof(f109,plain,(
% 2.22/0.98    v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 2.22/0.98    inference(definition_unfolding,[],[f94,f77])).
% 2.22/0.98  
% 2.22/0.98  fof(f13,axiom,(
% 2.22/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f22,plain,(
% 2.22/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.22/0.98    inference(pure_predicate_removal,[],[f13])).
% 2.22/0.98  
% 2.22/0.98  fof(f35,plain,(
% 2.22/0.98    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f22])).
% 2.22/0.98  
% 2.22/0.98  fof(f36,plain,(
% 2.22/0.98    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.22/0.98    inference(flattening,[],[f35])).
% 2.22/0.98  
% 2.22/0.98  fof(f81,plain,(
% 2.22/0.98    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f36])).
% 2.22/0.98  
% 2.22/0.98  fof(f100,plain,(
% 2.22/0.98    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(definition_unfolding,[],[f81,f77,f77,f77])).
% 2.22/0.98  
% 2.22/0.98  fof(f99,plain,(
% 2.22/0.98    ~r1_waybel_7(sK2,sK3,sK4) | ~r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4)),
% 2.22/0.98    inference(cnf_transformation,[],[f61])).
% 2.22/0.98  
% 2.22/0.98  fof(f16,axiom,(
% 2.22/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f41,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f16])).
% 2.22/0.98  
% 2.22/0.98  fof(f42,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.98    inference(flattening,[],[f41])).
% 2.22/0.98  
% 2.22/0.98  fof(f55,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.98    inference(nnf_transformation,[],[f42])).
% 2.22/0.98  
% 2.22/0.98  fof(f87,plain,(
% 2.22/0.98    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f55])).
% 2.22/0.98  
% 2.22/0.98  fof(f90,plain,(
% 2.22/0.98    v2_pre_topc(sK2)),
% 2.22/0.98    inference(cnf_transformation,[],[f61])).
% 2.22/0.98  
% 2.22/0.98  fof(f89,plain,(
% 2.22/0.98    ~v2_struct_0(sK2)),
% 2.22/0.98    inference(cnf_transformation,[],[f61])).
% 2.22/0.98  
% 2.22/0.98  fof(f91,plain,(
% 2.22/0.98    l1_pre_topc(sK2)),
% 2.22/0.98    inference(cnf_transformation,[],[f61])).
% 2.22/0.98  
% 2.22/0.98  fof(f97,plain,(
% 2.22/0.98    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.22/0.98    inference(cnf_transformation,[],[f61])).
% 2.22/0.98  
% 2.22/0.98  fof(f6,axiom,(
% 2.22/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f26,plain,(
% 2.22/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.22/0.98    inference(ennf_transformation,[],[f6])).
% 2.22/0.98  
% 2.22/0.98  fof(f68,plain,(
% 2.22/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f26])).
% 2.22/0.98  
% 2.22/0.98  fof(f95,plain,(
% 2.22/0.98    v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK2)))),
% 2.22/0.98    inference(cnf_transformation,[],[f61])).
% 2.22/0.98  
% 2.22/0.98  fof(f108,plain,(
% 2.22/0.98    v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))),
% 2.22/0.98    inference(definition_unfolding,[],[f95,f77])).
% 2.22/0.98  
% 2.22/0.98  fof(f92,plain,(
% 2.22/0.98    ~v1_xboole_0(sK3)),
% 2.22/0.98    inference(cnf_transformation,[],[f61])).
% 2.22/0.98  
% 2.22/0.98  fof(f7,axiom,(
% 2.22/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f27,plain,(
% 2.22/0.98    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f7])).
% 2.22/0.98  
% 2.22/0.98  fof(f28,plain,(
% 2.22/0.98    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.22/0.98    inference(flattening,[],[f27])).
% 2.22/0.98  
% 2.22/0.98  fof(f69,plain,(
% 2.22/0.98    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f28])).
% 2.22/0.98  
% 2.22/0.98  fof(f9,axiom,(
% 2.22/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f31,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.98    inference(ennf_transformation,[],[f9])).
% 2.22/0.98  
% 2.22/0.98  fof(f32,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.98    inference(flattening,[],[f31])).
% 2.22/0.98  
% 2.22/0.98  fof(f73,plain,(
% 2.22/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f32])).
% 2.22/0.98  
% 2.22/0.98  fof(f5,axiom,(
% 2.22/0.98    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f25,plain,(
% 2.22/0.98    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 2.22/0.98    inference(ennf_transformation,[],[f5])).
% 2.22/0.98  
% 2.22/0.98  fof(f67,plain,(
% 2.22/0.98    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f25])).
% 2.22/0.98  
% 2.22/0.98  fof(f10,axiom,(
% 2.22/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f33,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.98    inference(ennf_transformation,[],[f10])).
% 2.22/0.98  
% 2.22/0.98  fof(f53,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.98    inference(nnf_transformation,[],[f33])).
% 2.22/0.98  
% 2.22/0.98  fof(f76,plain,(
% 2.22/0.98    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f53])).
% 2.22/0.98  
% 2.22/0.98  fof(f12,axiom,(
% 2.22/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f34,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.98    inference(ennf_transformation,[],[f12])).
% 2.22/0.98  
% 2.22/0.98  fof(f54,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.22/0.98    inference(nnf_transformation,[],[f34])).
% 2.22/0.98  
% 2.22/0.98  fof(f78,plain,(
% 2.22/0.98    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f54])).
% 2.22/0.98  
% 2.22/0.98  fof(f96,plain,(
% 2.22/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK2)))))),
% 2.22/0.98    inference(cnf_transformation,[],[f61])).
% 2.22/0.98  
% 2.22/0.98  fof(f107,plain,(
% 2.22/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))),
% 2.22/0.98    inference(definition_unfolding,[],[f96,f77])).
% 2.22/0.98  
% 2.22/0.98  fof(f8,axiom,(
% 2.22/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f29,plain,(
% 2.22/0.98    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f8])).
% 2.22/0.98  
% 2.22/0.98  fof(f30,plain,(
% 2.22/0.98    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.98    inference(flattening,[],[f29])).
% 2.22/0.98  
% 2.22/0.98  fof(f51,plain,(
% 2.22/0.98    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK1(X0),X0) & ~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.22/0.98    introduced(choice_axiom,[])).
% 2.22/0.98  
% 2.22/0.98  fof(f52,plain,(
% 2.22/0.98    ! [X0] : ((v4_pre_topc(sK1(X0),X0) & ~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.22/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f51])).
% 2.22/0.98  
% 2.22/0.98  fof(f71,plain,(
% 2.22/0.98    ( ! [X0] : (~v1_xboole_0(sK1(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f52])).
% 2.22/0.98  
% 2.22/0.98  fof(f17,axiom,(
% 2.22/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f43,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f17])).
% 2.22/0.98  
% 2.22/0.98  fof(f44,plain,(
% 2.22/0.98    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.22/0.98    inference(flattening,[],[f43])).
% 2.22/0.98  
% 2.22/0.98  fof(f88,plain,(
% 2.22/0.98    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f44])).
% 2.22/0.98  
% 2.22/0.98  fof(f106,plain,(
% 2.22/0.98    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(definition_unfolding,[],[f88,f77,f77,f77,f77])).
% 2.22/0.98  
% 2.22/0.98  fof(f93,plain,(
% 2.22/0.98    v1_subset_1(sK3,u1_struct_0(k3_yellow_1(k2_struct_0(sK2))))),
% 2.22/0.98    inference(cnf_transformation,[],[f61])).
% 2.22/0.98  
% 2.22/0.98  fof(f110,plain,(
% 2.22/0.98    v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))),
% 2.22/0.98    inference(definition_unfolding,[],[f93,f77])).
% 2.22/0.98  
% 2.22/0.98  fof(f98,plain,(
% 2.22/0.98    r1_waybel_7(sK2,sK3,sK4) | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4)),
% 2.22/0.98    inference(cnf_transformation,[],[f61])).
% 2.22/0.98  
% 2.22/0.98  fof(f86,plain,(
% 2.22/0.98    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f55])).
% 2.22/0.98  
% 2.22/0.98  fof(f70,plain,(
% 2.22/0.98    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f52])).
% 2.22/0.98  
% 2.22/0.98  fof(f1,axiom,(
% 2.22/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f47,plain,(
% 2.22/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.22/0.98    inference(nnf_transformation,[],[f1])).
% 2.22/0.98  
% 2.22/0.98  fof(f48,plain,(
% 2.22/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.22/0.98    inference(rectify,[],[f47])).
% 2.22/0.98  
% 2.22/0.98  fof(f49,plain,(
% 2.22/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.22/0.98    introduced(choice_axiom,[])).
% 2.22/0.98  
% 2.22/0.98  fof(f50,plain,(
% 2.22/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.22/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f48,f49])).
% 2.22/0.98  
% 2.22/0.98  fof(f63,plain,(
% 2.22/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f50])).
% 2.22/0.98  
% 2.22/0.98  fof(f4,axiom,(
% 2.22/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f24,plain,(
% 2.22/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.22/0.98    inference(ennf_transformation,[],[f4])).
% 2.22/0.98  
% 2.22/0.98  fof(f66,plain,(
% 2.22/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f24])).
% 2.22/0.98  
% 2.22/0.98  fof(f15,axiom,(
% 2.22/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f21,plain,(
% 2.22/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.22/0.98    inference(pure_predicate_removal,[],[f15])).
% 2.22/0.98  
% 2.22/0.98  fof(f39,plain,(
% 2.22/0.98    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f21])).
% 2.22/0.98  
% 2.22/0.98  fof(f40,plain,(
% 2.22/0.98    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.22/0.98    inference(flattening,[],[f39])).
% 2.22/0.98  
% 2.22/0.98  fof(f85,plain,(
% 2.22/0.98    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f40])).
% 2.22/0.98  
% 2.22/0.98  fof(f104,plain,(
% 2.22/0.98    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(definition_unfolding,[],[f85,f77,f77,f77,f77])).
% 2.22/0.98  
% 2.22/0.98  fof(f14,axiom,(
% 2.22/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f20,plain,(
% 2.22/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.22/0.98    inference(pure_predicate_removal,[],[f14])).
% 2.22/0.98  
% 2.22/0.98  fof(f23,plain,(
% 2.22/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.22/0.98    inference(pure_predicate_removal,[],[f20])).
% 2.22/0.98  
% 2.22/0.98  fof(f37,plain,(
% 2.22/0.98    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.22/0.98    inference(ennf_transformation,[],[f23])).
% 2.22/0.98  
% 2.22/0.98  fof(f38,plain,(
% 2.22/0.98    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.22/0.98    inference(flattening,[],[f37])).
% 2.22/0.98  
% 2.22/0.98  fof(f83,plain,(
% 2.22/0.98    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f38])).
% 2.22/0.98  
% 2.22/0.98  fof(f102,plain,(
% 2.22/0.98    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(definition_unfolding,[],[f83,f77,f77,f77])).
% 2.22/0.98  
% 2.22/0.98  fof(f80,plain,(
% 2.22/0.98    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(cnf_transformation,[],[f36])).
% 2.22/0.98  
% 2.22/0.98  fof(f101,plain,(
% 2.22/0.98    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.22/0.98    inference(definition_unfolding,[],[f80,f77,f77,f77])).
% 2.22/0.98  
% 2.22/0.98  fof(f3,axiom,(
% 2.22/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f65,plain,(
% 2.22/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.22/0.98    inference(cnf_transformation,[],[f3])).
% 2.22/0.98  
% 2.22/0.98  fof(f2,axiom,(
% 2.22/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 2.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.22/0.98  
% 2.22/0.98  fof(f64,plain,(
% 2.22/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.22/0.98    inference(cnf_transformation,[],[f2])).
% 2.22/0.98  
% 2.22/0.98  cnf(c_31,negated_conjecture,
% 2.22/0.98      ( v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.22/0.98      inference(cnf_transformation,[],[f109]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_17,plain,
% 2.22/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.98      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 2.22/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.98      | v2_struct_0(X2)
% 2.22/0.98      | ~ l1_struct_0(X2)
% 2.22/0.98      | v1_xboole_0(X0)
% 2.22/0.98      | v1_xboole_0(X1) ),
% 2.22/0.98      inference(cnf_transformation,[],[f100]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_26,negated_conjecture,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.98      | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
% 2.22/0.98      inference(cnf_transformation,[],[f99]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_274,plain,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.98      | ~ r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
% 2.22/0.98      inference(prop_impl,[status(thm)],[c_26]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_23,plain,
% 2.22/0.98      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.22/0.98      | r3_waybel_9(X0,X1,X2)
% 2.22/0.98      | ~ l1_waybel_0(X1,X0)
% 2.22/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.98      | ~ v7_waybel_0(X1)
% 2.22/0.98      | ~ v4_orders_2(X1)
% 2.22/0.98      | v2_struct_0(X0)
% 2.22/0.98      | v2_struct_0(X1)
% 2.22/0.98      | ~ v2_pre_topc(X0)
% 2.22/0.98      | ~ l1_pre_topc(X0) ),
% 2.22/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_35,negated_conjecture,
% 2.22/0.98      ( v2_pre_topc(sK2) ),
% 2.22/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_737,plain,
% 2.22/0.98      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.22/0.98      | r3_waybel_9(X0,X1,X2)
% 2.22/0.98      | ~ l1_waybel_0(X1,X0)
% 2.22/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.98      | ~ v7_waybel_0(X1)
% 2.22/0.98      | ~ v4_orders_2(X1)
% 2.22/0.98      | v2_struct_0(X0)
% 2.22/0.98      | v2_struct_0(X1)
% 2.22/0.98      | ~ l1_pre_topc(X0)
% 2.22/0.98      | sK2 != X0 ),
% 2.22/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_738,plain,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.22/0.98      | r3_waybel_9(sK2,X0,X1)
% 2.22/0.98      | ~ l1_waybel_0(X0,sK2)
% 2.22/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.22/0.98      | ~ v7_waybel_0(X0)
% 2.22/0.98      | ~ v4_orders_2(X0)
% 2.22/0.98      | v2_struct_0(X0)
% 2.22/0.98      | v2_struct_0(sK2)
% 2.22/0.98      | ~ l1_pre_topc(sK2) ),
% 2.22/0.98      inference(unflattening,[status(thm)],[c_737]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_36,negated_conjecture,
% 2.22/0.98      ( ~ v2_struct_0(sK2) ),
% 2.22/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_34,negated_conjecture,
% 2.22/0.98      ( l1_pre_topc(sK2) ),
% 2.22/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_742,plain,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.22/0.98      | r3_waybel_9(sK2,X0,X1)
% 2.22/0.98      | ~ l1_waybel_0(X0,sK2)
% 2.22/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.22/0.98      | ~ v7_waybel_0(X0)
% 2.22/0.98      | ~ v4_orders_2(X0)
% 2.22/0.98      | v2_struct_0(X0) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_738,c_36,c_34]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1181,plain,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.22/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.98      | ~ l1_waybel_0(X0,sK2)
% 2.22/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.22/0.98      | ~ v7_waybel_0(X0)
% 2.22/0.98      | ~ v4_orders_2(X0)
% 2.22/0.98      | v2_struct_0(X0)
% 2.22/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != X0
% 2.22/0.98      | sK4 != X1
% 2.22/0.98      | sK2 != sK2 ),
% 2.22/0.98      inference(resolution_lifted,[status(thm)],[c_274,c_742]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1182,plain,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.98      | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.22/0.98      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.22/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.22/0.98      inference(unflattening,[status(thm)],[c_1181]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_28,negated_conjecture,
% 2.22/0.98      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.22/0.98      inference(cnf_transformation,[],[f97]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1184,plain,
% 2.22/0.98      ( ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.22/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.98      | ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.22/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1182,c_28]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1185,plain,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.98      | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.22/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.22/0.98      inference(renaming,[status(thm)],[c_1184]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1221,plain,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | v2_struct_0(X2)
% 2.22/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | ~ l1_struct_0(X2)
% 2.22/0.98      | v1_xboole_0(X0)
% 2.22/0.98      | v1_xboole_0(X1)
% 2.22/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(X2,X1,X0)
% 2.22/0.98      | sK2 != X2 ),
% 2.22/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_1185]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1222,plain,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | v2_struct_0(sK2)
% 2.22/0.98      | ~ l1_struct_0(sK2)
% 2.22/0.98      | v1_xboole_0(X0)
% 2.22/0.98      | v1_xboole_0(X1)
% 2.22/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
% 2.22/0.98      inference(unflattening,[status(thm)],[c_1221]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_6,plain,
% 2.22/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.22/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_104,plain,
% 2.22/0.98      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.22/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1226,plain,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | v1_xboole_0(X0)
% 2.22/0.98      | v1_xboole_0(X1)
% 2.22/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
% 2.22/0.98      inference(global_propositional_subsumption,
% 2.22/0.98                [status(thm)],
% 2.22/0.98                [c_1222,c_36,c_34,c_104]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_30,negated_conjecture,
% 2.22/0.98      ( v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.22/0.98      inference(cnf_transformation,[],[f108]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1805,plain,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.98      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.98      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.98      | v1_xboole_0(X0)
% 2.22/0.98      | v1_xboole_0(X1)
% 2.22/0.98      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0)
% 2.22/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.22/0.98      | sK3 != X0 ),
% 2.22/0.98      inference(resolution_lifted,[status(thm)],[c_1226,c_30]) ).
% 2.22/0.98  
% 2.22/0.98  cnf(c_1806,plain,
% 2.22/0.98      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(sK3)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_1805]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_33,negated_conjecture,
% 2.22/0.99      ( ~ v1_xboole_0(sK3) ),
% 2.22/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1810,plain,
% 2.22/0.99      ( v1_xboole_0(X0)
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1806,c_33]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1811,plain,
% 2.22/0.99      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_1810]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2154,plain,
% 2.22/0.99      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | sK3 != sK3 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_1811]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2710,plain,
% 2.22/0.99      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(equality_resolution_simp,[status(thm)],[c_2154]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3190,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | ~ sP0_iProver_split ),
% 2.22/0.99      inference(splitting,
% 2.22/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.22/0.99                [c_2710]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3551,plain,
% 2.22/0.99      ( k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.22/0.99      | v1_xboole_0(X0) = iProver_top
% 2.22/0.99      | sP0_iProver_split != iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_3190]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_7,plain,
% 2.22/0.99      ( v4_pre_topc(k2_struct_0(X0),X0)
% 2.22/0.99      | ~ v2_pre_topc(X0)
% 2.22/0.99      | ~ l1_pre_topc(X0) ),
% 2.22/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_12,plain,
% 2.22/0.99      ( ~ v4_pre_topc(X0,X1)
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.99      | ~ l1_pre_topc(X1)
% 2.22/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 2.22/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_588,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.99      | ~ v2_pre_topc(X2)
% 2.22/0.99      | ~ l1_pre_topc(X2)
% 2.22/0.99      | ~ l1_pre_topc(X1)
% 2.22/0.99      | X1 != X2
% 2.22/0.99      | k2_pre_topc(X1,X0) = X0
% 2.22/0.99      | k2_struct_0(X2) != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_589,plain,
% 2.22/0.99      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/0.99      | ~ v2_pre_topc(X0)
% 2.22/0.99      | ~ l1_pre_topc(X0)
% 2.22/0.99      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_588]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_5,plain,
% 2.22/0.99      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/0.99      | ~ l1_struct_0(X0) ),
% 2.22/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_593,plain,
% 2.22/0.99      ( ~ v2_pre_topc(X0)
% 2.22/0.99      | ~ l1_pre_topc(X0)
% 2.22/0.99      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 2.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_589,c_6,c_5]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_696,plain,
% 2.22/0.99      ( ~ l1_pre_topc(X0)
% 2.22/0.99      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
% 2.22/0.99      | sK2 != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_593,c_35]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_697,plain,
% 2.22/0.99      ( ~ l1_pre_topc(sK2)
% 2.22/0.99      | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_696]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_107,plain,
% 2.22/0.99      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ l1_struct_0(sK2) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_591,plain,
% 2.22/0.99      ( ~ m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v2_pre_topc(sK2)
% 2.22/0.99      | ~ l1_pre_topc(sK2)
% 2.22/0.99      | k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_589]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_699,plain,
% 2.22/0.99      ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_697,c_35,c_34,c_104,c_107,c_591]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_13,plain,
% 2.22/0.99      ( v1_tops_1(X0,X1)
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.99      | ~ l1_pre_topc(X1)
% 2.22/0.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 2.22/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_16,plain,
% 2.22/0.99      ( ~ v1_tops_1(X0,X1)
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.99      | ~ l1_pre_topc(X1)
% 2.22/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 2.22/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_660,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.99      | ~ l1_pre_topc(X1)
% 2.22/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 2.22/0.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 2.22/0.99      inference(resolution,[status(thm)],[c_13,c_16]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_821,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.99      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 2.22/0.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1)
% 2.22/0.99      | sK2 != X1 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_660,c_34]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_822,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
% 2.22/0.99      | k2_pre_topc(sK2,X0) != k2_struct_0(sK2) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_821]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3558,plain,
% 2.22/0.99      ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
% 2.22/0.99      | k2_pre_topc(sK2,X0) != k2_struct_0(sK2)
% 2.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_822]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4260,plain,
% 2.22/0.99      ( k2_pre_topc(sK2,k2_struct_0(sK2)) = u1_struct_0(sK2)
% 2.22/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.22/0.99      inference(superposition,[status(thm)],[c_699,c_3558]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4271,plain,
% 2.22/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2)
% 2.22/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.22/0.99      inference(light_normalisation,[status(thm)],[c_4260,c_699]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_39,plain,
% 2.22/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_103,plain,
% 2.22/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_105,plain,
% 2.22/0.99      ( l1_pre_topc(sK2) != iProver_top | l1_struct_0(sK2) = iProver_top ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_103]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_106,plain,
% 2.22/0.99      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.22/0.99      | l1_struct_0(X0) != iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_108,plain,
% 2.22/0.99      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.22/0.99      | l1_struct_0(sK2) != iProver_top ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_106]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4277,plain,
% 2.22/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_4271,c_39,c_105,c_108]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4552,plain,
% 2.22/0.99      ( k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.22/0.99      | v1_xboole_0(X0) = iProver_top
% 2.22/0.99      | sP0_iProver_split != iProver_top ),
% 2.22/0.99      inference(light_normalisation,[status(thm)],[c_3551,c_4277]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4562,plain,
% 2.22/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.22/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.22/0.99      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
% 2.22/0.99      | sP0_iProver_split != iProver_top ),
% 2.22/0.99      inference(equality_resolution,[status(thm)],[c_4552]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4629,plain,
% 2.22/0.99      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.22/0.99      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top
% 2.22/0.99      | sP0_iProver_split != iProver_top ),
% 2.22/0.99      inference(equality_resolution_simp,[status(thm)],[c_4562]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_37,plain,
% 2.22/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_38,plain,
% 2.22/0.99      ( v2_pre_topc(sK2) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_29,negated_conjecture,
% 2.22/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) ),
% 2.22/0.99      inference(cnf_transformation,[],[f107]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_44,plain,
% 2.22/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_9,plain,
% 2.22/0.99      ( v2_struct_0(X0)
% 2.22/0.99      | ~ v2_pre_topc(X0)
% 2.22/0.99      | ~ l1_pre_topc(X0)
% 2.22/0.99      | ~ v1_xboole_0(sK1(X0)) ),
% 2.22/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_94,plain,
% 2.22/0.99      ( v2_struct_0(X0) = iProver_top
% 2.22/0.99      | v2_pre_topc(X0) != iProver_top
% 2.22/0.99      | l1_pre_topc(X0) != iProver_top
% 2.22/0.99      | v1_xboole_0(sK1(X0)) != iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_96,plain,
% 2.22/0.99      ( v2_struct_0(sK2) = iProver_top
% 2.22/0.99      | v2_pre_topc(sK2) != iProver_top
% 2.22/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.22/0.99      | v1_xboole_0(sK1(sK2)) != iProver_top ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_94]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3191,plain,
% 2.22/0.99      ( ~ r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | ~ r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | sP0_iProver_split ),
% 2.22/0.99      inference(splitting,
% 2.22/0.99                [splitting(split),new_symbols(definition,[])],
% 2.22/0.99                [c_2710]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3550,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4) != iProver_top
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4) != iProver_top
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.22/0.99      | sP0_iProver_split = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_3191]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_25,plain,
% 2.22/0.99      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 2.22/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.22/0.99      | v2_struct_0(X1)
% 2.22/0.99      | ~ l1_struct_0(X1)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 2.22/0.99      inference(cnf_transformation,[],[f106]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_32,negated_conjecture,
% 2.22/0.99      ( v1_subset_1(sK3,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))) ),
% 2.22/0.99      inference(cnf_transformation,[],[f110]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_536,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.22/0.99      | v2_struct_0(X1)
% 2.22/0.99      | ~ l1_struct_0(X1)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.22/0.99      | sK3 != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_32]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_537,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | ~ l1_struct_0(X0)
% 2.22/0.99      | v1_xboole_0(sK3)
% 2.22/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_536]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_541,plain,
% 2.22/0.99      ( ~ l1_struct_0(X0)
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.22/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.22/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_537,c_33]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_542,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | ~ l1_struct_0(X0)
% 2.22/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_541]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_814,plain,
% 2.22/0.99      ( l1_struct_0(X0) | sK2 != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_34]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_815,plain,
% 2.22/0.99      ( l1_struct_0(sK2) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_814]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1319,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK3)) = sK3
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.22/0.99      | sK2 != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_542,c_815]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1320,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(k2_struct_0(sK2))))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2))))))
% 2.22/0.99      | v2_struct_0(sK2)
% 2.22/0.99      | k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_1319]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1322,plain,
% 2.22/0.99      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_1320,c_36,c_31,c_30,c_29]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2719,plain,
% 2.22/0.99      ( k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = sK3 ),
% 2.22/0.99      inference(equality_resolution_simp,[status(thm)],[c_1322]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3665,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,sK3,sK4) != iProver_top
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.22/0.99      | sP0_iProver_split = iProver_top ),
% 2.22/0.99      inference(light_normalisation,[status(thm)],[c_3550,c_2719]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_27,negated_conjecture,
% 2.22/0.99      ( r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
% 2.22/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_276,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | r3_waybel_9(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK4) ),
% 2.22/0.99      inference(prop_impl,[status(thm)],[c_27]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_24,plain,
% 2.22/0.99      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.22/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.22/0.99      | ~ l1_waybel_0(X1,X0)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | ~ v7_waybel_0(X1)
% 2.22/0.99      | ~ v4_orders_2(X1)
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | v2_struct_0(X1)
% 2.22/0.99      | ~ v2_pre_topc(X0)
% 2.22/0.99      | ~ l1_pre_topc(X0) ),
% 2.22/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_704,plain,
% 2.22/0.99      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.22/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 2.22/0.99      | ~ l1_waybel_0(X1,X0)
% 2.22/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.22/0.99      | ~ v7_waybel_0(X1)
% 2.22/0.99      | ~ v4_orders_2(X1)
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | v2_struct_0(X1)
% 2.22/0.99      | ~ l1_pre_topc(X0)
% 2.22/0.99      | sK2 != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_705,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.22/0.99      | ~ r3_waybel_9(sK2,X0,X1)
% 2.22/0.99      | ~ l1_waybel_0(X0,sK2)
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.22/0.99      | ~ v7_waybel_0(X0)
% 2.22/0.99      | ~ v4_orders_2(X0)
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | v2_struct_0(sK2)
% 2.22/0.99      | ~ l1_pre_topc(sK2) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_704]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_709,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.22/0.99      | ~ r3_waybel_9(sK2,X0,X1)
% 2.22/0.99      | ~ l1_waybel_0(X0,sK2)
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.22/0.99      | ~ v7_waybel_0(X0)
% 2.22/0.99      | ~ v4_orders_2(X0)
% 2.22/0.99      | v2_struct_0(X0) ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_705,c_36,c_34]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1155,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,X0),X1)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ l1_waybel_0(X0,sK2)
% 2.22/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.22/0.99      | ~ v7_waybel_0(X0)
% 2.22/0.99      | ~ v4_orders_2(X0)
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != X0
% 2.22/0.99      | sK4 != X1
% 2.22/0.99      | sK2 != sK2 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_276,c_709]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1156,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.22/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_1155]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1158,plain,
% 2.22/0.99      ( ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1156,c_28]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1159,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ l1_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3),sK2)
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_1158]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1269,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(X2)
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ l1_struct_0(X2)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(X2,X1,X0)
% 2.22/0.99      | sK2 != X2 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_1159]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1270,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(sK2)
% 2.22/0.99      | ~ l1_struct_0(sK2)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_1269]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1274,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0) ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_1270,c_36,c_34,c_104]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1760,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X1,X0)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.22/0.99      | sK3 != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_1274,c_30]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1761,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(sK3)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_1760]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1765,plain,
% 2.22/0.99      ( v1_xboole_0(X0)
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1761,c_33]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1766,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_1765]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2192,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | sK3 != sK3 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_1766]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2706,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_yellow19(sK2,k2_struct_0(sK2),sK3) != k3_yellow19(sK2,X0,sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(equality_resolution_simp,[status(thm)],[c_2192]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3192,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4)
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4)
% 2.22/0.99      | ~ v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | ~ v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3))
% 2.22/0.99      | sP0_iProver_split ),
% 2.22/0.99      inference(splitting,
% 2.22/0.99                [splitting(split),new_symbols(definition,[])],
% 2.22/0.99                [c_2706]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3552,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,k2_yellow19(sK2,k3_yellow19(sK2,k2_struct_0(sK2),sK3)),sK4) = iProver_top
% 2.22/0.99      | r1_waybel_7(sK2,sK3,sK4) = iProver_top
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.22/0.99      | sP0_iProver_split = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_3192]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3642,plain,
% 2.22/0.99      ( r1_waybel_7(sK2,sK3,sK4) = iProver_top
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.22/0.99      | sP0_iProver_split = iProver_top ),
% 2.22/0.99      inference(light_normalisation,[status(thm)],[c_3552,c_2719]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3671,plain,
% 2.22/0.99      ( v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.22/0.99      | sP0_iProver_split = iProver_top ),
% 2.22/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3665,c_3642]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_10,plain,
% 2.22/0.99      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | ~ v2_pre_topc(X0)
% 2.22/0.99      | ~ l1_pre_topc(X0) ),
% 2.22/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_770,plain,
% 2.22/0.99      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.22/0.99      | v2_struct_0(X0)
% 2.22/0.99      | ~ l1_pre_topc(X0)
% 2.22/0.99      | sK2 != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_35]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_771,plain,
% 2.22/0.99      ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | v2_struct_0(sK2)
% 2.22/0.99      | ~ l1_pre_topc(sK2) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_770]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_92,plain,
% 2.22/0.99      ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | v2_struct_0(sK2)
% 2.22/0.99      | ~ v2_pre_topc(sK2)
% 2.22/0.99      | ~ l1_pre_topc(sK2) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_773,plain,
% 2.22/0.99      ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_771,c_36,c_35,c_34,c_92]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3560,plain,
% 2.22/0.99      ( m1_subset_1(sK1(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4284,plain,
% 2.22/0.99      ( m1_subset_1(sK1(sK2),k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 2.22/0.99      inference(demodulation,[status(thm)],[c_4277,c_3560]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_0,plain,
% 2.22/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.22/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.22/0.99      | ~ r2_hidden(X2,X0)
% 2.22/0.99      | ~ v1_xboole_0(X1) ),
% 2.22/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_480,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.22/0.99      | ~ v1_xboole_0(X1)
% 2.22/0.99      | v1_xboole_0(X2)
% 2.22/0.99      | X0 != X2
% 2.22/0.99      | sK0(X2) != X3 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_481,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.22/0.99      | ~ v1_xboole_0(X1)
% 2.22/0.99      | v1_xboole_0(X0) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_480]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3561,plain,
% 2.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.22/0.99      | v1_xboole_0(X1) != iProver_top
% 2.22/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4359,plain,
% 2.22/0.99      ( v1_xboole_0(sK1(sK2)) = iProver_top
% 2.22/0.99      | v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
% 2.22/0.99      inference(superposition,[status(thm)],[c_4284,c_3561]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_21,plain,
% 2.22/0.99      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.22/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.22/0.99      | v2_struct_0(X2)
% 2.22/0.99      | ~ l1_struct_0(X2)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1) ),
% 2.22/0.99      inference(cnf_transformation,[],[f104]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_497,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.22/0.99      | v2_struct_0(X2)
% 2.22/0.99      | ~ l1_struct_0(X2)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1)
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | sK3 != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_498,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.22/0.99      | v2_struct_0(X1)
% 2.22/0.99      | ~ l1_struct_0(X1)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(sK3)
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_497]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_502,plain,
% 2.22/0.99      ( v1_xboole_0(X0)
% 2.22/0.99      | ~ l1_struct_0(X1)
% 2.22/0.99      | v2_struct_0(X1)
% 2.22/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_498,c_33]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_503,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.22/0.99      | v2_struct_0(X1)
% 2.22/0.99      | ~ l1_struct_0(X1)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_502]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1403,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK3))
% 2.22/0.99      | v2_struct_0(X1)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | sK2 != X1 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_503,c_815]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1404,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v2_struct_0(sK2)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_1403]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1408,plain,
% 2.22/0.99      ( v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1404,c_36]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1409,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ v13_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_1408]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1850,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | sK3 != sK3 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_1409]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2128,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | sK3 != sK3 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_1850]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2714,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.22/0.99      inference(equality_resolution_simp,[status(thm)],[c_2128]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3549,plain,
% 2.22/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,X0,sK3)) = iProver_top
% 2.22/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_2714]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4399,plain,
% 2.22/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,X0,sK3)) = iProver_top
% 2.22/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.22/0.99      inference(light_normalisation,[status(thm)],[c_3549,c_4277]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4409,plain,
% 2.22/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(k2_struct_0(sK2)))
% 2.22/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.22/0.99      | v7_waybel_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.22/0.99      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.22/0.99      inference(equality_resolution,[status(thm)],[c_4399]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_19,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.22/0.99      | v2_struct_0(X2)
% 2.22/0.99      | ~ l1_struct_0(X2)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1) ),
% 2.22/0.99      inference(cnf_transformation,[],[f102]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1337,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.22/0.99      | v2_struct_0(X2)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1)
% 2.22/0.99      | sK2 != X2 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_815]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1338,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,X1,X0))
% 2.22/0.99      | v2_struct_0(sK2)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_1337]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1342,plain,
% 2.22/0.99      ( v4_orders_2(k3_yellow19(sK2,X1,X0))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1) ),
% 2.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1338,c_36]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1343,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,X1,X0))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_1342]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1730,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,X1,X0))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.22/0.99      | sK3 != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_1343,c_30]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1731,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_1730]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1735,plain,
% 2.22/0.99      ( v1_xboole_0(X0)
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1731,c_33]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1736,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_1735]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2230,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | sK3 != sK3 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_1736]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2702,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(equality_resolution_simp,[status(thm)],[c_2230]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3554,plain,
% 2.22/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3)) = iProver_top
% 2.22/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_2702]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4412,plain,
% 2.22/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,X0,sK3)) = iProver_top
% 2.22/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.22/0.99      inference(light_normalisation,[status(thm)],[c_3554,c_4277]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4421,plain,
% 2.22/0.99      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.22/0.99      | v4_orders_2(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) = iProver_top
% 2.22/0.99      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.22/0.99      inference(equality_resolution,[status(thm)],[c_4412]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_18,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | v2_struct_0(X2)
% 2.22/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.22/0.99      | ~ l1_struct_0(X2)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1) ),
% 2.22/0.99      inference(cnf_transformation,[],[f101]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1370,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | v2_struct_0(X2)
% 2.22/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1)
% 2.22/0.99      | sK2 != X2 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_815]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1371,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
% 2.22/0.99      | v2_struct_0(sK2)
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_1370]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1375,plain,
% 2.22/0.99      ( ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1) ),
% 2.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1371,c_36]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1376,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_1375]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1700,plain,
% 2.22/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.22/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X1,X0))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(X1)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X1))
% 2.22/0.99      | sK3 != X0 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_1376,c_30]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1701,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | v1_xboole_0(sK3)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(unflattening,[status(thm)],[c_1700]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1705,plain,
% 2.22/0.99      ( v1_xboole_0(X0)
% 2.22/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1701,c_33]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_1706,plain,
% 2.22/0.99      ( ~ v2_waybel_0(sK3,k3_lattice3(k1_lattice3(X0)))
% 2.22/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_1705]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2253,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | sK3 != sK3 ),
% 2.22/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_1706]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2698,plain,
% 2.22/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.22/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.22/0.99      | ~ v2_struct_0(k3_yellow19(sK2,X0,sK3))
% 2.22/0.99      | v1_xboole_0(X0)
% 2.22/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.22/0.99      inference(equality_resolution_simp,[status(thm)],[c_2253]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3555,plain,
% 2.22/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,X0,sK3)) != iProver_top
% 2.22/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_2698]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4462,plain,
% 2.22/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) != k3_lattice3(k1_lattice3(X0))
% 2.22/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,X0,sK3)) != iProver_top
% 2.22/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.22/0.99      inference(light_normalisation,[status(thm)],[c_3555,c_4277]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4471,plain,
% 2.22/0.99      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.22/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK2)))))) != iProver_top
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 2.22/0.99      inference(equality_resolution,[status(thm)],[c_4462]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4570,plain,
% 2.22/0.99      ( v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top
% 2.22/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_4471,c_37,c_38,c_39,c_44,c_96,c_4359]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4571,plain,
% 2.22/0.99      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.22/0.99      | v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top ),
% 2.22/0.99      inference(renaming,[status(thm)],[c_4570]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3,plain,
% 2.22/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.22/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3566,plain,
% 2.22/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.22/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_2,plain,
% 2.22/0.99      ( k2_subset_1(X0) = X0 ),
% 2.22/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3581,plain,
% 2.22/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.22/0.99      inference(light_normalisation,[status(thm)],[c_3566,c_2]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4576,plain,
% 2.22/0.99      ( v2_struct_0(k3_yellow19(sK2,k2_struct_0(sK2),sK3)) != iProver_top ),
% 2.22/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4571,c_3581]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_3194,plain,( X0 = X0 ),theory(equality) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4617,plain,
% 2.22/0.99      ( k3_lattice3(k1_lattice3(k2_struct_0(sK2))) = k3_lattice3(k1_lattice3(k2_struct_0(sK2))) ),
% 2.22/0.99      inference(instantiation,[status(thm)],[c_3194]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4631,plain,
% 2.22/0.99      ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.22/0.99      inference(global_propositional_subsumption,
% 2.22/0.99                [status(thm)],
% 2.22/0.99                [c_4629,c_37,c_38,c_39,c_44,c_96,c_3671,c_4359,c_4409,c_4421,
% 2.22/0.99                 c_4576,c_4617]) ).
% 2.22/0.99  
% 2.22/0.99  cnf(c_4636,plain,
% 2.22/0.99      ( $false ),
% 2.22/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4631,c_3581]) ).
% 2.22/0.99  
% 2.22/0.99  
% 2.22/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.22/0.99  
% 2.22/0.99  ------                               Statistics
% 2.22/0.99  
% 2.22/0.99  ------ General
% 2.22/0.99  
% 2.22/0.99  abstr_ref_over_cycles:                  0
% 2.22/0.99  abstr_ref_under_cycles:                 0
% 2.22/0.99  gc_basic_clause_elim:                   0
% 2.22/0.99  forced_gc_time:                         0
% 2.22/0.99  parsing_time:                           0.011
% 2.22/0.99  unif_index_cands_time:                  0.
% 2.22/0.99  unif_index_add_time:                    0.
% 2.22/0.99  orderings_time:                         0.
% 2.22/0.99  out_proof_time:                         0.017
% 2.22/0.99  total_time:                             0.176
% 2.22/0.99  num_of_symbols:                         63
% 2.22/0.99  num_of_terms:                           2274
% 2.22/0.99  
% 2.22/0.99  ------ Preprocessing
% 2.22/0.99  
% 2.22/0.99  num_of_splits:                          2
% 2.22/0.99  num_of_split_atoms:                     1
% 2.22/0.99  num_of_reused_defs:                     1
% 2.22/0.99  num_eq_ax_congr_red:                    14
% 2.22/0.99  num_of_sem_filtered_clauses:            1
% 2.22/0.99  num_of_subtypes:                        0
% 2.22/0.99  monotx_restored_types:                  0
% 2.22/0.99  sat_num_of_epr_types:                   0
% 2.22/0.99  sat_num_of_non_cyclic_types:            0
% 2.22/0.99  sat_guarded_non_collapsed_types:        0
% 2.22/0.99  num_pure_diseq_elim:                    0
% 2.22/0.99  simp_replaced_by:                       0
% 2.22/0.99  res_preprocessed:                       132
% 2.22/0.99  prep_upred:                             0
% 2.22/0.99  prep_unflattend:                        42
% 2.22/0.99  smt_new_axioms:                         0
% 2.22/0.99  pred_elim_cands:                        6
% 2.22/0.99  pred_elim:                              11
% 2.22/0.99  pred_elim_cl:                           15
% 2.22/0.99  pred_elim_cycles:                       24
% 2.22/0.99  merged_defs:                            2
% 2.22/0.99  merged_defs_ncl:                        0
% 2.22/0.99  bin_hyper_res:                          2
% 2.22/0.99  prep_cycles:                            4
% 2.22/0.99  pred_elim_time:                         0.082
% 2.22/0.99  splitting_time:                         0.
% 2.22/0.99  sem_filter_time:                        0.
% 2.22/0.99  monotx_time:                            0.
% 2.22/0.99  subtype_inf_time:                       0.
% 2.22/0.99  
% 2.22/0.99  ------ Problem properties
% 2.22/0.99  
% 2.22/0.99  clauses:                                22
% 2.22/0.99  conjectures:                            4
% 2.22/0.99  epr:                                    2
% 2.22/0.99  horn:                                   18
% 2.22/0.99  ground:                                 12
% 2.22/0.99  unary:                                  12
% 2.22/0.99  binary:                                 0
% 2.22/0.99  lits:                                   61
% 2.22/0.99  lits_eq:                                16
% 2.22/0.99  fd_pure:                                0
% 2.22/0.99  fd_pseudo:                              0
% 2.22/0.99  fd_cond:                                0
% 2.22/0.99  fd_pseudo_cond:                         0
% 2.22/0.99  ac_symbols:                             0
% 2.22/0.99  
% 2.22/0.99  ------ Propositional Solver
% 2.22/0.99  
% 2.22/0.99  prop_solver_calls:                      26
% 2.22/0.99  prop_fast_solver_calls:                 1761
% 2.22/0.99  smt_solver_calls:                       0
% 2.22/0.99  smt_fast_solver_calls:                  0
% 2.22/0.99  prop_num_of_clauses:                    985
% 2.22/0.99  prop_preprocess_simplified:             3897
% 2.22/0.99  prop_fo_subsumed:                       49
% 2.22/0.99  prop_solver_time:                       0.
% 2.22/0.99  smt_solver_time:                        0.
% 2.22/0.99  smt_fast_solver_time:                   0.
% 2.22/0.99  prop_fast_solver_time:                  0.
% 2.22/0.99  prop_unsat_core_time:                   0.
% 2.22/0.99  
% 2.22/0.99  ------ QBF
% 2.22/0.99  
% 2.22/0.99  qbf_q_res:                              0
% 2.22/0.99  qbf_num_tautologies:                    0
% 2.22/0.99  qbf_prep_cycles:                        0
% 2.22/0.99  
% 2.22/0.99  ------ BMC1
% 2.22/0.99  
% 2.22/0.99  bmc1_current_bound:                     -1
% 2.22/0.99  bmc1_last_solved_bound:                 -1
% 2.22/0.99  bmc1_unsat_core_size:                   -1
% 2.22/0.99  bmc1_unsat_core_parents_size:           -1
% 2.22/0.99  bmc1_merge_next_fun:                    0
% 2.22/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.22/0.99  
% 2.22/0.99  ------ Instantiation
% 2.22/0.99  
% 2.22/0.99  inst_num_of_clauses:                    210
% 2.22/0.99  inst_num_in_passive:                    32
% 2.22/0.99  inst_num_in_active:                     135
% 2.22/0.99  inst_num_in_unprocessed:                43
% 2.22/0.99  inst_num_of_loops:                      140
% 2.22/0.99  inst_num_of_learning_restarts:          0
% 2.22/0.99  inst_num_moves_active_passive:          3
% 2.22/0.99  inst_lit_activity:                      0
% 2.22/0.99  inst_lit_activity_moves:                0
% 2.22/0.99  inst_num_tautologies:                   0
% 2.22/0.99  inst_num_prop_implied:                  0
% 2.22/0.99  inst_num_existing_simplified:           0
% 2.22/0.99  inst_num_eq_res_simplified:             0
% 2.22/0.99  inst_num_child_elim:                    0
% 2.22/0.99  inst_num_of_dismatching_blockings:      45
% 2.22/0.99  inst_num_of_non_proper_insts:           150
% 2.22/0.99  inst_num_of_duplicates:                 0
% 2.22/0.99  inst_inst_num_from_inst_to_res:         0
% 2.22/0.99  inst_dismatching_checking_time:         0.
% 2.22/0.99  
% 2.22/0.99  ------ Resolution
% 2.22/0.99  
% 2.22/0.99  res_num_of_clauses:                     0
% 2.22/0.99  res_num_in_passive:                     0
% 2.22/0.99  res_num_in_active:                      0
% 2.22/0.99  res_num_of_loops:                       136
% 2.22/0.99  res_forward_subset_subsumed:            20
% 2.22/0.99  res_backward_subset_subsumed:           0
% 2.22/0.99  res_forward_subsumed:                   0
% 2.22/0.99  res_backward_subsumed:                  0
% 2.22/0.99  res_forward_subsumption_resolution:     2
% 2.22/0.99  res_backward_subsumption_resolution:    0
% 2.22/0.99  res_clause_to_clause_subsumption:       314
% 2.22/0.99  res_orphan_elimination:                 0
% 2.22/0.99  res_tautology_del:                      27
% 2.22/0.99  res_num_eq_res_simplified:              6
% 2.22/0.99  res_num_sel_changes:                    0
% 2.22/0.99  res_moves_from_active_to_pass:          0
% 2.22/0.99  
% 2.22/0.99  ------ Superposition
% 2.22/0.99  
% 2.22/0.99  sup_time_total:                         0.
% 2.22/0.99  sup_time_generating:                    0.
% 2.22/0.99  sup_time_sim_full:                      0.
% 2.22/0.99  sup_time_sim_immed:                     0.
% 2.22/0.99  
% 2.22/0.99  sup_num_of_clauses:                     23
% 2.22/0.99  sup_num_in_active:                      20
% 2.22/0.99  sup_num_in_passive:                     3
% 2.22/0.99  sup_num_of_loops:                       26
% 2.22/0.99  sup_fw_superposition:                   8
% 2.22/0.99  sup_bw_superposition:                   1
% 2.22/0.99  sup_immediate_simplified:               5
% 2.22/0.99  sup_given_eliminated:                   0
% 2.22/0.99  comparisons_done:                       0
% 2.22/0.99  comparisons_avoided:                    0
% 2.22/0.99  
% 2.22/0.99  ------ Simplifications
% 2.22/0.99  
% 2.22/0.99  
% 2.22/0.99  sim_fw_subset_subsumed:                 1
% 2.22/0.99  sim_bw_subset_subsumed:                 0
% 2.22/0.99  sim_fw_subsumed:                        1
% 2.22/0.99  sim_bw_subsumed:                        1
% 2.22/0.99  sim_fw_subsumption_res:                 3
% 2.22/0.99  sim_bw_subsumption_res:                 0
% 2.22/0.99  sim_tautology_del:                      5
% 2.22/0.99  sim_eq_tautology_del:                   0
% 2.22/0.99  sim_eq_res_simp:                        1
% 2.22/0.99  sim_fw_demodulated:                     2
% 2.22/0.99  sim_bw_demodulated:                     6
% 2.22/0.99  sim_light_normalised:                   10
% 2.22/0.99  sim_joinable_taut:                      0
% 2.22/0.99  sim_joinable_simp:                      0
% 2.22/0.99  sim_ac_normalised:                      0
% 2.22/0.99  sim_smt_subsumption:                    0
% 2.22/0.99  
%------------------------------------------------------------------------------
