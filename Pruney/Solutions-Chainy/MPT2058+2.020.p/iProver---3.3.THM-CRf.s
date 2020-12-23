%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:18 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  208 (1894 expanded)
%              Number of clauses        :  136 ( 416 expanded)
%              Number of leaves         :   14 ( 520 expanded)
%              Depth                    :   35
%              Number of atoms          : 1379 (16566 expanded)
%              Number of equality atoms :  195 ( 443 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f35,plain,(
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).

fof(f60,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f60,f45])).

fof(f6,axiom,(
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
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f47,plain,(
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

fof(f66,plain,(
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
    inference(definition_unfolding,[],[f47,f45,f45,f45])).

fof(f65,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f34,plain,(
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

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f61,f45])).

fof(f58,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

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
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f49,plain,(
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

fof(f68,plain,(
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
    inference(definition_unfolding,[],[f49,f45,f45,f45])).

fof(f8,axiom,(
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

fof(f15,plain,(
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
    inference(pure_predicate_removal,[],[f8])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f51,plain,(
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

fof(f70,plain,(
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
    inference(definition_unfolding,[],[f51,f45,f45,f45,f45])).

fof(f59,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f59,f45])).

fof(f46,plain,(
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

fof(f67,plain,(
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
    inference(definition_unfolding,[],[f46,f45,f45,f45])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f54,plain,(
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

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f54,f45,f45,f45,f45])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f40])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f62,f45])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f34])).

cnf(c_18,negated_conjecture,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,negated_conjecture,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_175,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_442,plain,
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
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_443,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_447,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_23,c_21])).

cnf(c_820,plain,
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
    inference(resolution_lifted,[status(thm)],[c_175,c_447])).

cnf(c_821,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_820])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_823,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_821,c_15])).

cnf(c_824,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_823])).

cnf(c_860,plain,
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
    inference(resolution_lifted,[status(thm)],[c_4,c_824])).

cnf(c_861,plain,
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
    inference(unflattening,[status(thm)],[c_860])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_64,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_865,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_861,c_23,c_21,c_64])).

cnf(c_866,plain,
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
    inference(renaming,[status(thm)],[c_865])).

cnf(c_17,negated_conjecture,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1463,plain,
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
    inference(resolution_lifted,[status(thm)],[c_866,c_17])).

cnf(c_1464,plain,
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
    inference(unflattening,[status(thm)],[c_1463])).

cnf(c_20,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1468,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1464,c_20])).

cnf(c_1469,plain,
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
    inference(renaming,[status(thm)],[c_1468])).

cnf(c_1812,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_1469])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_491,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_21])).

cnf(c_492,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_969,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_492])).

cnf(c_970,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_969])).

cnf(c_61,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_972,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_970,c_23,c_21,c_61,c_64])).

cnf(c_2516,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1812,c_972])).

cnf(c_2517,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2516])).

cnf(c_6,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_992,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_492])).

cnf(c_993,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_992])).

cnf(c_997,plain,
    ( v4_orders_2(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_993,c_23])).

cnf(c_998,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_997])).

cnf(c_1388,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_998,c_17])).

cnf(c_1389,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1388])).

cnf(c_1393,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1389,c_20])).

cnf(c_1394,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1393])).

cnf(c_1888,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_1394])).

cnf(c_2469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1888,c_972])).

cnf(c_2470,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v4_orders_2(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2469])).

cnf(c_2770,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_2517,c_2470])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f70])).

cnf(c_19,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_319,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_320,plain,
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
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_324,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_20])).

cnf(c_325,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_324])).

cnf(c_1058,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_325,c_492])).

cnf(c_1059,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1058])).

cnf(c_1063,plain,
    ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1059,c_23])).

cnf(c_1064,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1063])).

cnf(c_1508,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1064])).

cnf(c_1786,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_1508])).

cnf(c_2547,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1786,c_972])).

cnf(c_2548,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v7_waybel_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_2547])).

cnf(c_3031,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_2770,c_2548])).

cnf(c_5,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1025,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_492])).

cnf(c_1026,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1025])).

cnf(c_1030,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1026,c_23])).

cnf(c_1031,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1030])).

cnf(c_1358,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1031,c_17])).

cnf(c_1359,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1358])).

cnf(c_1363,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1359,c_20])).

cnf(c_1364,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1363])).

cnf(c_1911,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_1364])).

cnf(c_2453,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1911,c_972])).

cnf(c_2454,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v2_struct_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2453])).

cnf(c_3334,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_3031,c_2454])).

cnf(c_3483,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_3334])).

cnf(c_3650,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
    | r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3483])).

cnf(c_12,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_358,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_359,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_363,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_20])).

cnf(c_364,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_958,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_364,c_492])).

cnf(c_959,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_958])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_961,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_959,c_23,c_18,c_17,c_16])).

cnf(c_3438,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_961])).

cnf(c_3481,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_3438])).

cnf(c_0,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_987,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_492])).

cnf(c_988,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_987])).

cnf(c_3486,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_988])).

cnf(c_3697,plain,
    ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3650,c_3481,c_3486])).

cnf(c_3698,plain,
    ( r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3697])).

cnf(c_3488,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3646,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3488])).

cnf(c_1,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_980,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_492])).

cnf(c_981,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_980])).

cnf(c_3487,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_981])).

cnf(c_3647,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3487])).

cnf(c_3657,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3647,c_3486])).

cnf(c_14,negated_conjecture,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_177,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f52])).

cnf(c_409,plain,
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
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_410,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_414,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_23,c_21])).

cnf(c_794,plain,
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
    inference(resolution_lifted,[status(thm)],[c_177,c_414])).

cnf(c_795,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_794])).

cnf(c_797,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,sK1,sK2)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_795,c_15])).

cnf(c_798,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_797])).

cnf(c_908,plain,
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
    inference(resolution_lifted,[status(thm)],[c_4,c_798])).

cnf(c_909,plain,
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
    inference(unflattening,[status(thm)],[c_908])).

cnf(c_913,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_909,c_23,c_21,c_64])).

cnf(c_914,plain,
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
    inference(renaming,[status(thm)],[c_913])).

cnf(c_1418,plain,
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
    inference(resolution_lifted,[status(thm)],[c_914,c_17])).

cnf(c_1419,plain,
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
    inference(unflattening,[status(thm)],[c_1418])).

cnf(c_1423,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1419,c_20])).

cnf(c_1424,plain,
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
    inference(renaming,[status(thm)],[c_1423])).

cnf(c_1850,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_1424])).

cnf(c_2485,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1850,c_972])).

cnf(c_2486,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2485])).

cnf(c_2797,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(resolution_lifted,[status(thm)],[c_2486,c_2470])).

cnf(c_3004,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_2797,c_2548])).

cnf(c_3358,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(resolution_lifted,[status(thm)],[c_3004,c_2454])).

cnf(c_3482,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
    | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_3358])).

cnf(c_3651,plain,
    ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3482])).

cnf(c_3690,plain,
    ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3651,c_3481,c_3486])).

cnf(c_3691,plain,
    ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3690])).

cnf(c_3695,plain,
    ( r1_waybel_7(sK0,sK1,sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3691,c_3646,c_3657])).

cnf(c_3702,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3698,c_3646,c_3657,c_3695])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.82/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/0.98  
% 1.82/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.82/0.98  
% 1.82/0.98  ------  iProver source info
% 1.82/0.98  
% 1.82/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.82/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.82/0.98  git: non_committed_changes: false
% 1.82/0.98  git: last_make_outside_of_git: false
% 1.82/0.98  
% 1.82/0.98  ------ 
% 1.82/0.98  
% 1.82/0.98  ------ Input Options
% 1.82/0.98  
% 1.82/0.98  --out_options                           all
% 1.82/0.98  --tptp_safe_out                         true
% 1.82/0.98  --problem_path                          ""
% 1.82/0.98  --include_path                          ""
% 1.82/0.98  --clausifier                            res/vclausify_rel
% 1.82/0.98  --clausifier_options                    --mode clausify
% 1.82/0.98  --stdin                                 false
% 1.82/0.98  --stats_out                             all
% 1.82/0.98  
% 1.82/0.98  ------ General Options
% 1.82/0.98  
% 1.82/0.98  --fof                                   false
% 1.82/0.98  --time_out_real                         305.
% 1.82/0.98  --time_out_virtual                      -1.
% 1.82/0.98  --symbol_type_check                     false
% 1.82/0.98  --clausify_out                          false
% 1.82/0.98  --sig_cnt_out                           false
% 1.82/0.98  --trig_cnt_out                          false
% 1.82/0.98  --trig_cnt_out_tolerance                1.
% 1.82/0.98  --trig_cnt_out_sk_spl                   false
% 1.82/0.98  --abstr_cl_out                          false
% 1.82/0.98  
% 1.82/0.98  ------ Global Options
% 1.82/0.98  
% 1.82/0.98  --schedule                              default
% 1.82/0.98  --add_important_lit                     false
% 1.82/0.98  --prop_solver_per_cl                    1000
% 1.82/0.98  --min_unsat_core                        false
% 1.82/0.98  --soft_assumptions                      false
% 1.82/0.98  --soft_lemma_size                       3
% 1.82/0.98  --prop_impl_unit_size                   0
% 1.82/0.98  --prop_impl_unit                        []
% 1.82/0.98  --share_sel_clauses                     true
% 1.82/0.98  --reset_solvers                         false
% 1.82/0.98  --bc_imp_inh                            [conj_cone]
% 1.82/0.98  --conj_cone_tolerance                   3.
% 1.82/0.98  --extra_neg_conj                        none
% 1.82/0.98  --large_theory_mode                     true
% 1.82/0.98  --prolific_symb_bound                   200
% 1.82/0.98  --lt_threshold                          2000
% 1.82/0.98  --clause_weak_htbl                      true
% 1.82/0.98  --gc_record_bc_elim                     false
% 1.92/0.98  
% 1.92/0.98  ------ Preprocessing Options
% 1.92/0.98  
% 1.92/0.98  --preprocessing_flag                    true
% 1.92/0.98  --time_out_prep_mult                    0.1
% 1.92/0.98  --splitting_mode                        input
% 1.92/0.98  --splitting_grd                         true
% 1.92/0.98  --splitting_cvd                         false
% 1.92/0.98  --splitting_cvd_svl                     false
% 1.92/0.98  --splitting_nvd                         32
% 1.92/0.98  --sub_typing                            true
% 1.92/0.98  --prep_gs_sim                           true
% 1.92/0.98  --prep_unflatten                        true
% 1.92/0.98  --prep_res_sim                          true
% 1.92/0.98  --prep_upred                            true
% 1.92/0.98  --prep_sem_filter                       exhaustive
% 1.92/0.98  --prep_sem_filter_out                   false
% 1.92/0.98  --pred_elim                             true
% 1.92/0.98  --res_sim_input                         true
% 1.92/0.98  --eq_ax_congr_red                       true
% 1.92/0.98  --pure_diseq_elim                       true
% 1.92/0.98  --brand_transform                       false
% 1.92/0.98  --non_eq_to_eq                          false
% 1.92/0.98  --prep_def_merge                        true
% 1.92/0.98  --prep_def_merge_prop_impl              false
% 1.92/0.98  --prep_def_merge_mbd                    true
% 1.92/0.98  --prep_def_merge_tr_red                 false
% 1.92/0.98  --prep_def_merge_tr_cl                  false
% 1.92/0.98  --smt_preprocessing                     true
% 1.92/0.98  --smt_ac_axioms                         fast
% 1.92/0.98  --preprocessed_out                      false
% 1.92/0.98  --preprocessed_stats                    false
% 1.92/0.98  
% 1.92/0.98  ------ Abstraction refinement Options
% 1.92/0.98  
% 1.92/0.98  --abstr_ref                             []
% 1.92/0.98  --abstr_ref_prep                        false
% 1.92/0.98  --abstr_ref_until_sat                   false
% 1.92/0.98  --abstr_ref_sig_restrict                funpre
% 1.92/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.92/0.98  --abstr_ref_under                       []
% 1.92/0.98  
% 1.92/0.98  ------ SAT Options
% 1.92/0.98  
% 1.92/0.98  --sat_mode                              false
% 1.92/0.98  --sat_fm_restart_options                ""
% 1.92/0.98  --sat_gr_def                            false
% 1.92/0.98  --sat_epr_types                         true
% 1.92/0.98  --sat_non_cyclic_types                  false
% 1.92/0.98  --sat_finite_models                     false
% 1.92/0.98  --sat_fm_lemmas                         false
% 1.92/0.98  --sat_fm_prep                           false
% 1.92/0.98  --sat_fm_uc_incr                        true
% 1.92/0.98  --sat_out_model                         small
% 1.92/0.98  --sat_out_clauses                       false
% 1.92/0.98  
% 1.92/0.98  ------ QBF Options
% 1.92/0.98  
% 1.92/0.98  --qbf_mode                              false
% 1.92/0.98  --qbf_elim_univ                         false
% 1.92/0.98  --qbf_dom_inst                          none
% 1.92/0.98  --qbf_dom_pre_inst                      false
% 1.92/0.98  --qbf_sk_in                             false
% 1.92/0.98  --qbf_pred_elim                         true
% 1.92/0.98  --qbf_split                             512
% 1.92/0.98  
% 1.92/0.98  ------ BMC1 Options
% 1.92/0.98  
% 1.92/0.98  --bmc1_incremental                      false
% 1.92/0.98  --bmc1_axioms                           reachable_all
% 1.92/0.98  --bmc1_min_bound                        0
% 1.92/0.98  --bmc1_max_bound                        -1
% 1.92/0.98  --bmc1_max_bound_default                -1
% 1.92/0.98  --bmc1_symbol_reachability              true
% 1.92/0.98  --bmc1_property_lemmas                  false
% 1.92/0.98  --bmc1_k_induction                      false
% 1.92/0.98  --bmc1_non_equiv_states                 false
% 1.92/0.98  --bmc1_deadlock                         false
% 1.92/0.98  --bmc1_ucm                              false
% 1.92/0.98  --bmc1_add_unsat_core                   none
% 1.92/0.98  --bmc1_unsat_core_children              false
% 1.92/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.92/0.98  --bmc1_out_stat                         full
% 1.92/0.98  --bmc1_ground_init                      false
% 1.92/0.98  --bmc1_pre_inst_next_state              false
% 1.92/0.98  --bmc1_pre_inst_state                   false
% 1.92/0.98  --bmc1_pre_inst_reach_state             false
% 1.92/0.98  --bmc1_out_unsat_core                   false
% 1.92/0.98  --bmc1_aig_witness_out                  false
% 1.92/0.98  --bmc1_verbose                          false
% 1.92/0.98  --bmc1_dump_clauses_tptp                false
% 1.92/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.92/0.98  --bmc1_dump_file                        -
% 1.92/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.92/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.92/0.98  --bmc1_ucm_extend_mode                  1
% 1.92/0.98  --bmc1_ucm_init_mode                    2
% 1.92/0.98  --bmc1_ucm_cone_mode                    none
% 1.92/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.92/0.98  --bmc1_ucm_relax_model                  4
% 1.92/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.92/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.92/0.98  --bmc1_ucm_layered_model                none
% 1.92/0.98  --bmc1_ucm_max_lemma_size               10
% 1.92/0.98  
% 1.92/0.98  ------ AIG Options
% 1.92/0.98  
% 1.92/0.98  --aig_mode                              false
% 1.92/0.98  
% 1.92/0.98  ------ Instantiation Options
% 1.92/0.98  
% 1.92/0.98  --instantiation_flag                    true
% 1.92/0.98  --inst_sos_flag                         false
% 1.92/0.98  --inst_sos_phase                        true
% 1.92/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.92/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.92/0.98  --inst_lit_sel_side                     num_symb
% 1.92/0.98  --inst_solver_per_active                1400
% 1.92/0.98  --inst_solver_calls_frac                1.
% 1.92/0.98  --inst_passive_queue_type               priority_queues
% 1.92/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.92/0.98  --inst_passive_queues_freq              [25;2]
% 1.92/0.98  --inst_dismatching                      true
% 1.92/0.98  --inst_eager_unprocessed_to_passive     true
% 1.92/0.98  --inst_prop_sim_given                   true
% 1.92/0.98  --inst_prop_sim_new                     false
% 1.92/0.98  --inst_subs_new                         false
% 1.92/0.98  --inst_eq_res_simp                      false
% 1.92/0.98  --inst_subs_given                       false
% 1.92/0.98  --inst_orphan_elimination               true
% 1.92/0.98  --inst_learning_loop_flag               true
% 1.92/0.98  --inst_learning_start                   3000
% 1.92/0.98  --inst_learning_factor                  2
% 1.92/0.98  --inst_start_prop_sim_after_learn       3
% 1.92/0.98  --inst_sel_renew                        solver
% 1.92/0.98  --inst_lit_activity_flag                true
% 1.92/0.98  --inst_restr_to_given                   false
% 1.92/0.98  --inst_activity_threshold               500
% 1.92/0.98  --inst_out_proof                        true
% 1.92/0.98  
% 1.92/0.98  ------ Resolution Options
% 1.92/0.98  
% 1.92/0.98  --resolution_flag                       true
% 1.92/0.98  --res_lit_sel                           adaptive
% 1.92/0.98  --res_lit_sel_side                      none
% 1.92/0.98  --res_ordering                          kbo
% 1.92/0.98  --res_to_prop_solver                    active
% 1.92/0.98  --res_prop_simpl_new                    false
% 1.92/0.98  --res_prop_simpl_given                  true
% 1.92/0.98  --res_passive_queue_type                priority_queues
% 1.92/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.92/0.98  --res_passive_queues_freq               [15;5]
% 1.92/0.98  --res_forward_subs                      full
% 1.92/0.98  --res_backward_subs                     full
% 1.92/0.98  --res_forward_subs_resolution           true
% 1.92/0.98  --res_backward_subs_resolution          true
% 1.92/0.98  --res_orphan_elimination                true
% 1.92/0.98  --res_time_limit                        2.
% 1.92/0.98  --res_out_proof                         true
% 1.92/0.98  
% 1.92/0.98  ------ Superposition Options
% 1.92/0.98  
% 1.92/0.98  --superposition_flag                    true
% 1.92/0.98  --sup_passive_queue_type                priority_queues
% 1.92/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.92/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.92/0.98  --demod_completeness_check              fast
% 1.92/0.98  --demod_use_ground                      true
% 1.92/0.98  --sup_to_prop_solver                    passive
% 1.92/0.98  --sup_prop_simpl_new                    true
% 1.92/0.98  --sup_prop_simpl_given                  true
% 1.92/0.98  --sup_fun_splitting                     false
% 1.92/0.98  --sup_smt_interval                      50000
% 1.92/0.98  
% 1.92/0.98  ------ Superposition Simplification Setup
% 1.92/0.98  
% 1.92/0.98  --sup_indices_passive                   []
% 1.92/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.92/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.98  --sup_full_bw                           [BwDemod]
% 1.92/0.98  --sup_immed_triv                        [TrivRules]
% 1.92/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.92/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.98  --sup_immed_bw_main                     []
% 1.92/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.92/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/0.98  
% 1.92/0.98  ------ Combination Options
% 1.92/0.98  
% 1.92/0.98  --comb_res_mult                         3
% 1.92/0.98  --comb_sup_mult                         2
% 1.92/0.98  --comb_inst_mult                        10
% 1.92/0.98  
% 1.92/0.98  ------ Debug Options
% 1.92/0.98  
% 1.92/0.98  --dbg_backtrace                         false
% 1.92/0.98  --dbg_dump_prop_clauses                 false
% 1.92/0.98  --dbg_dump_prop_clauses_file            -
% 1.92/0.98  --dbg_out_stat                          false
% 1.92/0.98  ------ Parsing...
% 1.92/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.92/0.98  
% 1.92/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 1.92/0.98  
% 1.92/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.92/0.98  
% 1.92/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.92/0.98  ------ Proving...
% 1.92/0.98  ------ Problem Properties 
% 1.92/0.98  
% 1.92/0.98  
% 1.92/0.98  clauses                                 9
% 1.92/0.98  conjectures                             2
% 1.92/0.98  EPR                                     0
% 1.92/0.98  Horn                                    7
% 1.92/0.98  unary                                   5
% 1.92/0.98  binary                                  0
% 1.92/0.98  lits                                    33
% 1.92/0.98  lits eq                                 14
% 1.92/0.98  fd_pure                                 0
% 1.92/0.98  fd_pseudo                               0
% 1.92/0.98  fd_cond                                 0
% 1.92/0.98  fd_pseudo_cond                          0
% 1.92/0.98  AC symbols                              0
% 1.92/0.98  
% 1.92/0.98  ------ Schedule dynamic 5 is on 
% 1.92/0.98  
% 1.92/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.92/0.98  
% 1.92/0.98  
% 1.92/0.98  ------ 
% 1.92/0.98  Current options:
% 1.92/0.98  ------ 
% 1.92/0.98  
% 1.92/0.98  ------ Input Options
% 1.92/0.98  
% 1.92/0.98  --out_options                           all
% 1.92/0.98  --tptp_safe_out                         true
% 1.92/0.98  --problem_path                          ""
% 1.92/0.98  --include_path                          ""
% 1.92/0.98  --clausifier                            res/vclausify_rel
% 1.92/0.98  --clausifier_options                    --mode clausify
% 1.92/0.98  --stdin                                 false
% 1.92/0.98  --stats_out                             all
% 1.92/0.98  
% 1.92/0.98  ------ General Options
% 1.92/0.98  
% 1.92/0.98  --fof                                   false
% 1.92/0.98  --time_out_real                         305.
% 1.92/0.98  --time_out_virtual                      -1.
% 1.92/0.98  --symbol_type_check                     false
% 1.92/0.98  --clausify_out                          false
% 1.92/0.98  --sig_cnt_out                           false
% 1.92/0.98  --trig_cnt_out                          false
% 1.92/0.98  --trig_cnt_out_tolerance                1.
% 1.92/0.98  --trig_cnt_out_sk_spl                   false
% 1.92/0.98  --abstr_cl_out                          false
% 1.92/0.98  
% 1.92/0.98  ------ Global Options
% 1.92/0.98  
% 1.92/0.98  --schedule                              default
% 1.92/0.98  --add_important_lit                     false
% 1.92/0.98  --prop_solver_per_cl                    1000
% 1.92/0.98  --min_unsat_core                        false
% 1.92/0.98  --soft_assumptions                      false
% 1.92/0.98  --soft_lemma_size                       3
% 1.92/0.98  --prop_impl_unit_size                   0
% 1.92/0.98  --prop_impl_unit                        []
% 1.92/0.98  --share_sel_clauses                     true
% 1.92/0.98  --reset_solvers                         false
% 1.92/0.98  --bc_imp_inh                            [conj_cone]
% 1.92/0.98  --conj_cone_tolerance                   3.
% 1.92/0.98  --extra_neg_conj                        none
% 1.92/0.98  --large_theory_mode                     true
% 1.92/0.98  --prolific_symb_bound                   200
% 1.92/0.98  --lt_threshold                          2000
% 1.92/0.98  --clause_weak_htbl                      true
% 1.92/0.98  --gc_record_bc_elim                     false
% 1.92/0.98  
% 1.92/0.98  ------ Preprocessing Options
% 1.92/0.98  
% 1.92/0.98  --preprocessing_flag                    true
% 1.92/0.98  --time_out_prep_mult                    0.1
% 1.92/0.98  --splitting_mode                        input
% 1.92/0.98  --splitting_grd                         true
% 1.92/0.98  --splitting_cvd                         false
% 1.92/0.98  --splitting_cvd_svl                     false
% 1.92/0.98  --splitting_nvd                         32
% 1.92/0.98  --sub_typing                            true
% 1.92/0.98  --prep_gs_sim                           true
% 1.92/0.98  --prep_unflatten                        true
% 1.92/0.98  --prep_res_sim                          true
% 1.92/0.98  --prep_upred                            true
% 1.92/0.98  --prep_sem_filter                       exhaustive
% 1.92/0.98  --prep_sem_filter_out                   false
% 1.92/0.98  --pred_elim                             true
% 1.92/0.98  --res_sim_input                         true
% 1.92/0.98  --eq_ax_congr_red                       true
% 1.92/0.98  --pure_diseq_elim                       true
% 1.92/0.98  --brand_transform                       false
% 1.92/0.98  --non_eq_to_eq                          false
% 1.92/0.98  --prep_def_merge                        true
% 1.92/0.98  --prep_def_merge_prop_impl              false
% 1.92/0.98  --prep_def_merge_mbd                    true
% 1.92/0.98  --prep_def_merge_tr_red                 false
% 1.92/0.98  --prep_def_merge_tr_cl                  false
% 1.92/0.98  --smt_preprocessing                     true
% 1.92/0.98  --smt_ac_axioms                         fast
% 1.92/0.98  --preprocessed_out                      false
% 1.92/0.98  --preprocessed_stats                    false
% 1.92/0.98  
% 1.92/0.98  ------ Abstraction refinement Options
% 1.92/0.98  
% 1.92/0.98  --abstr_ref                             []
% 1.92/0.98  --abstr_ref_prep                        false
% 1.92/0.98  --abstr_ref_until_sat                   false
% 1.92/0.98  --abstr_ref_sig_restrict                funpre
% 1.92/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.92/0.98  --abstr_ref_under                       []
% 1.92/0.98  
% 1.92/0.98  ------ SAT Options
% 1.92/0.98  
% 1.92/0.98  --sat_mode                              false
% 1.92/0.98  --sat_fm_restart_options                ""
% 1.92/0.98  --sat_gr_def                            false
% 1.92/0.98  --sat_epr_types                         true
% 1.92/0.98  --sat_non_cyclic_types                  false
% 1.92/0.98  --sat_finite_models                     false
% 1.92/0.98  --sat_fm_lemmas                         false
% 1.92/0.98  --sat_fm_prep                           false
% 1.92/0.98  --sat_fm_uc_incr                        true
% 1.92/0.98  --sat_out_model                         small
% 1.92/0.98  --sat_out_clauses                       false
% 1.92/0.98  
% 1.92/0.98  ------ QBF Options
% 1.92/0.98  
% 1.92/0.98  --qbf_mode                              false
% 1.92/0.98  --qbf_elim_univ                         false
% 1.92/0.98  --qbf_dom_inst                          none
% 1.92/0.98  --qbf_dom_pre_inst                      false
% 1.92/0.98  --qbf_sk_in                             false
% 1.92/0.98  --qbf_pred_elim                         true
% 1.92/0.98  --qbf_split                             512
% 1.92/0.98  
% 1.92/0.98  ------ BMC1 Options
% 1.92/0.98  
% 1.92/0.98  --bmc1_incremental                      false
% 1.92/0.98  --bmc1_axioms                           reachable_all
% 1.92/0.98  --bmc1_min_bound                        0
% 1.92/0.98  --bmc1_max_bound                        -1
% 1.92/0.98  --bmc1_max_bound_default                -1
% 1.92/0.98  --bmc1_symbol_reachability              true
% 1.92/0.98  --bmc1_property_lemmas                  false
% 1.92/0.98  --bmc1_k_induction                      false
% 1.92/0.98  --bmc1_non_equiv_states                 false
% 1.92/0.98  --bmc1_deadlock                         false
% 1.92/0.98  --bmc1_ucm                              false
% 1.92/0.98  --bmc1_add_unsat_core                   none
% 1.92/0.98  --bmc1_unsat_core_children              false
% 1.92/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.92/0.98  --bmc1_out_stat                         full
% 1.92/0.98  --bmc1_ground_init                      false
% 1.92/0.98  --bmc1_pre_inst_next_state              false
% 1.92/0.98  --bmc1_pre_inst_state                   false
% 1.92/0.98  --bmc1_pre_inst_reach_state             false
% 1.92/0.98  --bmc1_out_unsat_core                   false
% 1.92/0.98  --bmc1_aig_witness_out                  false
% 1.92/0.98  --bmc1_verbose                          false
% 1.92/0.98  --bmc1_dump_clauses_tptp                false
% 1.92/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.92/0.98  --bmc1_dump_file                        -
% 1.92/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.92/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.92/0.98  --bmc1_ucm_extend_mode                  1
% 1.92/0.98  --bmc1_ucm_init_mode                    2
% 1.92/0.98  --bmc1_ucm_cone_mode                    none
% 1.92/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.92/0.98  --bmc1_ucm_relax_model                  4
% 1.92/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.92/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.92/0.98  --bmc1_ucm_layered_model                none
% 1.92/0.98  --bmc1_ucm_max_lemma_size               10
% 1.92/0.98  
% 1.92/0.98  ------ AIG Options
% 1.92/0.98  
% 1.92/0.98  --aig_mode                              false
% 1.92/0.98  
% 1.92/0.98  ------ Instantiation Options
% 1.92/0.98  
% 1.92/0.98  --instantiation_flag                    true
% 1.92/0.98  --inst_sos_flag                         false
% 1.92/0.98  --inst_sos_phase                        true
% 1.92/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.92/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.92/0.98  --inst_lit_sel_side                     none
% 1.92/0.98  --inst_solver_per_active                1400
% 1.92/0.98  --inst_solver_calls_frac                1.
% 1.92/0.98  --inst_passive_queue_type               priority_queues
% 1.92/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.92/0.99  --inst_passive_queues_freq              [25;2]
% 1.92/0.99  --inst_dismatching                      true
% 1.92/0.99  --inst_eager_unprocessed_to_passive     true
% 1.92/0.99  --inst_prop_sim_given                   true
% 1.92/0.99  --inst_prop_sim_new                     false
% 1.92/0.99  --inst_subs_new                         false
% 1.92/0.99  --inst_eq_res_simp                      false
% 1.92/0.99  --inst_subs_given                       false
% 1.92/0.99  --inst_orphan_elimination               true
% 1.92/0.99  --inst_learning_loop_flag               true
% 1.92/0.99  --inst_learning_start                   3000
% 1.92/0.99  --inst_learning_factor                  2
% 1.92/0.99  --inst_start_prop_sim_after_learn       3
% 1.92/0.99  --inst_sel_renew                        solver
% 1.92/0.99  --inst_lit_activity_flag                true
% 1.92/0.99  --inst_restr_to_given                   false
% 1.92/0.99  --inst_activity_threshold               500
% 1.92/0.99  --inst_out_proof                        true
% 1.92/0.99  
% 1.92/0.99  ------ Resolution Options
% 1.92/0.99  
% 1.92/0.99  --resolution_flag                       false
% 1.92/0.99  --res_lit_sel                           adaptive
% 1.92/0.99  --res_lit_sel_side                      none
% 1.92/0.99  --res_ordering                          kbo
% 1.92/0.99  --res_to_prop_solver                    active
% 1.92/0.99  --res_prop_simpl_new                    false
% 1.92/0.99  --res_prop_simpl_given                  true
% 1.92/0.99  --res_passive_queue_type                priority_queues
% 1.92/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.92/0.99  --res_passive_queues_freq               [15;5]
% 1.92/0.99  --res_forward_subs                      full
% 1.92/0.99  --res_backward_subs                     full
% 1.92/0.99  --res_forward_subs_resolution           true
% 1.92/0.99  --res_backward_subs_resolution          true
% 1.92/0.99  --res_orphan_elimination                true
% 1.92/0.99  --res_time_limit                        2.
% 1.92/0.99  --res_out_proof                         true
% 1.92/0.99  
% 1.92/0.99  ------ Superposition Options
% 1.92/0.99  
% 1.92/0.99  --superposition_flag                    true
% 1.92/0.99  --sup_passive_queue_type                priority_queues
% 1.92/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.92/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.92/0.99  --demod_completeness_check              fast
% 1.92/0.99  --demod_use_ground                      true
% 1.92/0.99  --sup_to_prop_solver                    passive
% 1.92/0.99  --sup_prop_simpl_new                    true
% 1.92/0.99  --sup_prop_simpl_given                  true
% 1.92/0.99  --sup_fun_splitting                     false
% 1.92/0.99  --sup_smt_interval                      50000
% 1.92/0.99  
% 1.92/0.99  ------ Superposition Simplification Setup
% 1.92/0.99  
% 1.92/0.99  --sup_indices_passive                   []
% 1.92/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.92/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.99  --sup_full_bw                           [BwDemod]
% 1.92/0.99  --sup_immed_triv                        [TrivRules]
% 1.92/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.92/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.99  --sup_immed_bw_main                     []
% 1.92/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.92/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/0.99  
% 1.92/0.99  ------ Combination Options
% 1.92/0.99  
% 1.92/0.99  --comb_res_mult                         3
% 1.92/0.99  --comb_sup_mult                         2
% 1.92/0.99  --comb_inst_mult                        10
% 1.92/0.99  
% 1.92/0.99  ------ Debug Options
% 1.92/0.99  
% 1.92/0.99  --dbg_backtrace                         false
% 1.92/0.99  --dbg_dump_prop_clauses                 false
% 1.92/0.99  --dbg_dump_prop_clauses_file            -
% 1.92/0.99  --dbg_out_stat                          false
% 1.92/0.99  
% 1.92/0.99  
% 1.92/0.99  
% 1.92/0.99  
% 1.92/0.99  ------ Proving...
% 1.92/0.99  
% 1.92/0.99  
% 1.92/0.99  % SZS status Theorem for theBenchmark.p
% 1.92/0.99  
% 1.92/0.99   Resolution empty clause
% 1.92/0.99  
% 1.92/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.92/0.99  
% 1.92/0.99  fof(f11,conjecture,(
% 1.92/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/0.99  
% 1.92/0.99  fof(f12,negated_conjecture,(
% 1.92/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.92/0.99    inference(negated_conjecture,[],[f11])).
% 1.92/0.99  
% 1.92/0.99  fof(f32,plain,(
% 1.92/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.92/0.99    inference(ennf_transformation,[],[f12])).
% 1.92/0.99  
% 1.92/0.99  fof(f33,plain,(
% 1.92/0.99    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.92/0.99    inference(flattening,[],[f32])).
% 1.92/0.99  
% 1.92/0.99  fof(f35,plain,(
% 1.92/0.99    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.92/0.99    inference(nnf_transformation,[],[f33])).
% 1.92/0.99  
% 1.92/0.99  fof(f36,plain,(
% 1.92/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.92/0.99    inference(flattening,[],[f35])).
% 1.92/0.99  
% 1.92/0.99  fof(f39,plain,(
% 1.92/0.99    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & (r1_waybel_7(X0,X1,sK2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.92/0.99    introduced(choice_axiom,[])).
% 1.92/0.99  
% 1.92/0.99  fof(f38,plain,(
% 1.92/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & (r1_waybel_7(X0,sK1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK1))) )),
% 1.92/0.99    introduced(choice_axiom,[])).
% 1.92/0.99  
% 1.92/0.99  fof(f37,plain,(
% 1.92/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.92/0.99    introduced(choice_axiom,[])).
% 1.92/0.99  
% 1.92/0.99  fof(f40,plain,(
% 1.92/0.99    (((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).
% 1.92/0.99  
% 1.92/0.99  fof(f60,plain,(
% 1.92/0.99    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.92/0.99    inference(cnf_transformation,[],[f40])).
% 1.92/0.99  
% 1.92/0.99  fof(f5,axiom,(
% 1.92/0.99    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/0.99  
% 1.92/0.99  fof(f45,plain,(
% 1.92/0.99    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.92/0.99    inference(cnf_transformation,[],[f5])).
% 1.92/0.99  
% 1.92/0.99  fof(f75,plain,(
% 1.92/0.99    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.92/0.99    inference(definition_unfolding,[],[f60,f45])).
% 1.92/0.99  
% 1.92/0.99  fof(f6,axiom,(
% 1.92/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/0.99  
% 1.92/0.99  fof(f14,plain,(
% 1.92/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.92/0.99    inference(pure_predicate_removal,[],[f6])).
% 1.92/0.99  
% 1.92/0.99  fof(f22,plain,(
% 1.92/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.92/0.99    inference(ennf_transformation,[],[f14])).
% 1.92/0.99  
% 1.92/0.99  fof(f23,plain,(
% 1.92/0.99    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.92/0.99    inference(flattening,[],[f22])).
% 1.92/0.99  
% 1.92/0.99  fof(f47,plain,(
% 1.92/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(cnf_transformation,[],[f23])).
% 1.92/0.99  
% 1.92/0.99  fof(f66,plain,(
% 1.92/0.99    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(definition_unfolding,[],[f47,f45,f45,f45])).
% 1.92/0.99  
% 1.92/0.99  fof(f65,plain,(
% 1.92/0.99    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.92/0.99    inference(cnf_transformation,[],[f40])).
% 1.92/0.99  
% 1.92/0.99  fof(f9,axiom,(
% 1.92/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 1.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/0.99  
% 1.92/0.99  fof(f28,plain,(
% 1.92/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.92/0.99    inference(ennf_transformation,[],[f9])).
% 1.92/0.99  
% 1.92/0.99  fof(f29,plain,(
% 1.92/0.99    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.99    inference(flattening,[],[f28])).
% 1.92/0.99  
% 1.92/0.99  fof(f34,plain,(
% 1.92/0.99    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.92/0.99    inference(nnf_transformation,[],[f29])).
% 1.92/0.99  
% 1.92/0.99  fof(f53,plain,(
% 1.92/0.99    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(cnf_transformation,[],[f34])).
% 1.92/0.99  
% 1.92/0.99  fof(f56,plain,(
% 1.92/0.99    v2_pre_topc(sK0)),
% 1.92/0.99    inference(cnf_transformation,[],[f40])).
% 1.92/0.99  
% 1.92/0.99  fof(f55,plain,(
% 1.92/0.99    ~v2_struct_0(sK0)),
% 1.92/0.99    inference(cnf_transformation,[],[f40])).
% 1.92/0.99  
% 1.92/0.99  fof(f57,plain,(
% 1.92/0.99    l1_pre_topc(sK0)),
% 1.92/0.99    inference(cnf_transformation,[],[f40])).
% 1.92/0.99  
% 1.92/0.99  fof(f63,plain,(
% 1.92/0.99    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.92/0.99    inference(cnf_transformation,[],[f40])).
% 1.92/0.99  
% 1.92/0.99  fof(f3,axiom,(
% 1.92/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/0.99  
% 1.92/0.99  fof(f19,plain,(
% 1.92/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.92/0.99    inference(ennf_transformation,[],[f3])).
% 1.92/0.99  
% 1.92/0.99  fof(f43,plain,(
% 1.92/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.92/0.99    inference(cnf_transformation,[],[f19])).
% 1.92/0.99  
% 1.92/0.99  fof(f61,plain,(
% 1.92/0.99    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.92/0.99    inference(cnf_transformation,[],[f40])).
% 1.92/0.99  
% 1.92/0.99  fof(f74,plain,(
% 1.92/0.99    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.92/0.99    inference(definition_unfolding,[],[f61,f45])).
% 1.92/0.99  
% 1.92/0.99  fof(f58,plain,(
% 1.92/0.99    ~v1_xboole_0(sK1)),
% 1.92/0.99    inference(cnf_transformation,[],[f40])).
% 1.92/0.99  
% 1.92/0.99  fof(f4,axiom,(
% 1.92/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/0.99  
% 1.92/0.99  fof(f20,plain,(
% 1.92/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.92/0.99    inference(ennf_transformation,[],[f4])).
% 1.92/0.99  
% 1.92/0.99  fof(f21,plain,(
% 1.92/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.92/0.99    inference(flattening,[],[f20])).
% 1.92/0.99  
% 1.92/0.99  fof(f44,plain,(
% 1.92/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(cnf_transformation,[],[f21])).
% 1.92/0.99  
% 1.92/0.99  fof(f7,axiom,(
% 1.92/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/0.99  
% 1.92/0.99  fof(f13,plain,(
% 1.92/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.92/0.99    inference(pure_predicate_removal,[],[f7])).
% 1.92/0.99  
% 1.92/0.99  fof(f16,plain,(
% 1.92/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.92/0.99    inference(pure_predicate_removal,[],[f13])).
% 1.92/0.99  
% 1.92/0.99  fof(f24,plain,(
% 1.92/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.92/0.99    inference(ennf_transformation,[],[f16])).
% 1.92/0.99  
% 1.92/0.99  fof(f25,plain,(
% 1.92/0.99    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.92/0.99    inference(flattening,[],[f24])).
% 1.92/0.99  
% 1.92/0.99  fof(f49,plain,(
% 1.92/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(cnf_transformation,[],[f25])).
% 1.92/0.99  
% 1.92/0.99  fof(f68,plain,(
% 1.92/0.99    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(definition_unfolding,[],[f49,f45,f45,f45])).
% 1.92/0.99  
% 1.92/0.99  fof(f8,axiom,(
% 1.92/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/0.99  
% 1.92/0.99  fof(f15,plain,(
% 1.92/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.92/0.99    inference(pure_predicate_removal,[],[f8])).
% 1.92/0.99  
% 1.92/0.99  fof(f26,plain,(
% 1.92/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.92/0.99    inference(ennf_transformation,[],[f15])).
% 1.92/0.99  
% 1.92/0.99  fof(f27,plain,(
% 1.92/0.99    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.92/0.99    inference(flattening,[],[f26])).
% 1.92/0.99  
% 1.92/0.99  fof(f51,plain,(
% 1.92/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(cnf_transformation,[],[f27])).
% 1.92/0.99  
% 1.92/0.99  fof(f70,plain,(
% 1.92/0.99    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(definition_unfolding,[],[f51,f45,f45,f45,f45])).
% 1.92/0.99  
% 1.92/0.99  fof(f59,plain,(
% 1.92/0.99    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.92/0.99    inference(cnf_transformation,[],[f40])).
% 1.92/0.99  
% 1.92/0.99  fof(f76,plain,(
% 1.92/0.99    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.92/0.99    inference(definition_unfolding,[],[f59,f45])).
% 1.92/0.99  
% 1.92/0.99  fof(f46,plain,(
% 1.92/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(cnf_transformation,[],[f23])).
% 1.92/0.99  
% 1.92/0.99  fof(f67,plain,(
% 1.92/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(definition_unfolding,[],[f46,f45,f45,f45])).
% 1.92/0.99  
% 1.92/0.99  fof(f10,axiom,(
% 1.92/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/0.99  
% 1.92/0.99  fof(f30,plain,(
% 1.92/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.92/0.99    inference(ennf_transformation,[],[f10])).
% 1.92/0.99  
% 1.92/0.99  fof(f31,plain,(
% 1.92/0.99    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.92/0.99    inference(flattening,[],[f30])).
% 1.92/0.99  
% 1.92/0.99  fof(f54,plain,(
% 1.92/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(cnf_transformation,[],[f31])).
% 1.92/0.99  
% 1.92/0.99  fof(f72,plain,(
% 1.92/0.99    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(definition_unfolding,[],[f54,f45,f45,f45,f45])).
% 1.92/0.99  
% 1.92/0.99  fof(f62,plain,(
% 1.92/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.92/0.99    inference(cnf_transformation,[],[f40])).
% 1.92/0.99  
% 1.92/0.99  fof(f73,plain,(
% 1.92/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.92/0.99    inference(definition_unfolding,[],[f62,f45])).
% 1.92/0.99  
% 1.92/0.99  fof(f1,axiom,(
% 1.92/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/0.99  
% 1.92/0.99  fof(f17,plain,(
% 1.92/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.92/0.99    inference(ennf_transformation,[],[f1])).
% 1.92/0.99  
% 1.92/0.99  fof(f41,plain,(
% 1.92/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.92/0.99    inference(cnf_transformation,[],[f17])).
% 1.92/0.99  
% 1.92/0.99  fof(f2,axiom,(
% 1.92/0.99    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.92/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.92/0.99  
% 1.92/0.99  fof(f18,plain,(
% 1.92/0.99    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.92/0.99    inference(ennf_transformation,[],[f2])).
% 1.92/0.99  
% 1.92/0.99  fof(f42,plain,(
% 1.92/0.99    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.92/0.99    inference(cnf_transformation,[],[f18])).
% 1.92/0.99  
% 1.92/0.99  fof(f64,plain,(
% 1.92/0.99    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.92/0.99    inference(cnf_transformation,[],[f40])).
% 1.92/0.99  
% 1.92/0.99  fof(f52,plain,(
% 1.92/0.99    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.92/0.99    inference(cnf_transformation,[],[f34])).
% 1.92/0.99  
% 1.92/0.99  cnf(c_18,negated_conjecture,
% 1.92/0.99      ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(cnf_transformation,[],[f75]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_4,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | v2_struct_0(X2)
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(X2) ),
% 1.92/0.99      inference(cnf_transformation,[],[f66]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_13,negated_conjecture,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.92/0.99      inference(cnf_transformation,[],[f65]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_175,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.92/0.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_10,plain,
% 1.92/0.99      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.92/0.99      | r3_waybel_9(X0,X1,X2)
% 1.92/0.99      | ~ l1_waybel_0(X1,X0)
% 1.92/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.92/0.99      | ~ v2_pre_topc(X0)
% 1.92/0.99      | ~ v7_waybel_0(X1)
% 1.92/0.99      | ~ v4_orders_2(X1)
% 1.92/0.99      | v2_struct_0(X0)
% 1.92/0.99      | v2_struct_0(X1)
% 1.92/0.99      | ~ l1_pre_topc(X0) ),
% 1.92/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_22,negated_conjecture,
% 1.92/0.99      ( v2_pre_topc(sK0) ),
% 1.92/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_442,plain,
% 1.92/0.99      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.92/0.99      | r3_waybel_9(X0,X1,X2)
% 1.92/0.99      | ~ l1_waybel_0(X1,X0)
% 1.92/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.92/0.99      | ~ v7_waybel_0(X1)
% 1.92/0.99      | ~ v4_orders_2(X1)
% 1.92/0.99      | v2_struct_0(X0)
% 1.92/0.99      | v2_struct_0(X1)
% 1.92/0.99      | ~ l1_pre_topc(X0)
% 1.92/0.99      | sK0 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_443,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.92/0.99      | r3_waybel_9(sK0,X0,X1)
% 1.92/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.92/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.92/0.99      | ~ v7_waybel_0(X0)
% 1.92/0.99      | ~ v4_orders_2(X0)
% 1.92/0.99      | v2_struct_0(X0)
% 1.92/0.99      | v2_struct_0(sK0)
% 1.92/0.99      | ~ l1_pre_topc(sK0) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_442]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_23,negated_conjecture,
% 1.92/0.99      ( ~ v2_struct_0(sK0) ),
% 1.92/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_21,negated_conjecture,
% 1.92/0.99      ( l1_pre_topc(sK0) ),
% 1.92/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_447,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.92/0.99      | r3_waybel_9(sK0,X0,X1)
% 1.92/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.92/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.92/0.99      | ~ v7_waybel_0(X0)
% 1.92/0.99      | ~ v4_orders_2(X0)
% 1.92/0.99      | v2_struct_0(X0) ),
% 1.92/0.99      inference(global_propositional_subsumption,
% 1.92/0.99                [status(thm)],
% 1.92/0.99                [c_443,c_23,c_21]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_820,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.92/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.92/0.99      | ~ v7_waybel_0(X0)
% 1.92/0.99      | ~ v4_orders_2(X0)
% 1.92/0.99      | v2_struct_0(X0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 1.92/0.99      | sK2 != X1
% 1.92/0.99      | sK0 != sK0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_175,c_447]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_821,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.92/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_820]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_15,negated_conjecture,
% 1.92/0.99      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 1.92/0.99      inference(cnf_transformation,[],[f63]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_823,plain,
% 1.92/0.99      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.92/0.99      inference(global_propositional_subsumption,[status(thm)],[c_821,c_15]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_824,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_823]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_860,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(X2)
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(X2)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 1.92/0.99      | sK0 != X2 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_824]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_861,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(sK0)
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(sK0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_860]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2,plain,
% 1.92/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.92/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_64,plain,
% 1.92/0.99      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.92/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_865,plain,
% 1.92/0.99      ( v1_xboole_0(X0)
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.92/0.99      inference(global_propositional_subsumption,
% 1.92/0.99                [status(thm)],
% 1.92/0.99                [c_861,c_23,c_21,c_64]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_866,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_865]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_17,negated_conjecture,
% 1.92/0.99      ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(cnf_transformation,[],[f74]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1463,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.92/0.99      | sK1 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_866,c_17]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1464,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | v1_xboole_0(sK1)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_1463]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_20,negated_conjecture,
% 1.92/0.99      ( ~ v1_xboole_0(sK1) ),
% 1.92/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1468,plain,
% 1.92/0.99      ( v1_xboole_0(X0)
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1464,c_20]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1469,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_1468]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1812,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.92/0.99      | sK1 != sK1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_1469]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3,plain,
% 1.92/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 1.92/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_491,plain,
% 1.92/0.99      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_21]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_492,plain,
% 1.92/0.99      ( l1_struct_0(sK0) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_491]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_969,plain,
% 1.92/0.99      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK0 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_492]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_970,plain,
% 1.92/0.99      ( v2_struct_0(sK0) | ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_969]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_61,plain,
% 1.92/0.99      ( v2_struct_0(sK0)
% 1.92/0.99      | ~ v1_xboole_0(u1_struct_0(sK0))
% 1.92/0.99      | ~ l1_struct_0(sK0) ),
% 1.92/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_972,plain,
% 1.92/0.99      ( ~ v1_xboole_0(u1_struct_0(sK0)) ),
% 1.92/0.99      inference(global_propositional_subsumption,
% 1.92/0.99                [status(thm)],
% 1.92/0.99                [c_970,c_23,c_21,c_61,c_64]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2516,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.92/0.99      | u1_struct_0(sK0) != X0
% 1.92/0.99      | sK1 != sK1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_1812,c_972]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2517,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_2516]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_6,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.92/0.99      | v2_struct_0(X2)
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(X2) ),
% 1.92/0.99      inference(cnf_transformation,[],[f68]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_992,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.92/0.99      | v2_struct_0(X2)
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | sK0 != X2 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_492]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_993,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.92/0.99      | v2_struct_0(sK0)
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_992]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_997,plain,
% 1.92/0.99      ( v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0) ),
% 1.92/0.99      inference(global_propositional_subsumption,[status(thm)],[c_993,c_23]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_998,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_997]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1388,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.92/0.99      | sK1 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_998,c_17]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1389,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | v1_xboole_0(sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_1388]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1393,plain,
% 1.92/0.99      ( v1_xboole_0(X0)
% 1.92/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1389,c_20]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1394,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_1393]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1888,plain,
% 1.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.92/0.99      | sK1 != sK1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_1394]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2469,plain,
% 1.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.92/0.99      | u1_struct_0(sK0) != X0
% 1.92/0.99      | sK1 != sK1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_1888,c_972]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2470,plain,
% 1.92/0.99      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | v4_orders_2(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_2469]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2770,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_2517,c_2470]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_8,plain,
% 1.92/0.99      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.92/0.99      | v2_struct_0(X2)
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(X2) ),
% 1.92/0.99      inference(cnf_transformation,[],[f70]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_19,negated_conjecture,
% 1.92/0.99      ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
% 1.92/0.99      inference(cnf_transformation,[],[f76]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_319,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.92/0.99      | v2_struct_0(X2)
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(X2)
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | sK1 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_320,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.92/0.99      | v2_struct_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | v1_xboole_0(sK1)
% 1.92/0.99      | ~ l1_struct_0(X1)
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_319]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_324,plain,
% 1.92/0.99      ( v1_xboole_0(X0)
% 1.92/0.99      | v2_struct_0(X1)
% 1.92/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ l1_struct_0(X1)
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.92/0.99      inference(global_propositional_subsumption,[status(thm)],[c_320,c_20]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_325,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.92/0.99      | v2_struct_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(X1)
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_324]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1058,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.92/0.99      | v2_struct_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | sK0 != X1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_325,c_492]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1059,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | v2_struct_0(sK0)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_1058]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1063,plain,
% 1.92/0.99      ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.92/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1059,c_23]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1064,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_1063]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1508,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | sK1 != sK1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_1064]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1786,plain,
% 1.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | sK1 != sK1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_1508]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2547,plain,
% 1.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | u1_struct_0(sK0) != X0
% 1.92/0.99      | sK1 != sK1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_1786,c_972]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2548,plain,
% 1.92/0.99      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | v7_waybel_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0)))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_2547]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3031,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_2770,c_2548]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_5,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | v2_struct_0(X2)
% 1.92/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(X2) ),
% 1.92/0.99      inference(cnf_transformation,[],[f67]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1025,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | v2_struct_0(X2)
% 1.92/0.99      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | sK0 != X2 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_492]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1026,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.92/0.99      | v2_struct_0(sK0)
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_1025]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1030,plain,
% 1.92/0.99      ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0) ),
% 1.92/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1026,c_23]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1031,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_1030]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1358,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.92/0.99      | sK1 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_1031,c_17]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1359,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | v1_xboole_0(sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_1358]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1363,plain,
% 1.92/0.99      ( v1_xboole_0(X0)
% 1.92/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1359,c_20]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1364,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_1363]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1911,plain,
% 1.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.92/0.99      | sK1 != sK1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_1364]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2453,plain,
% 1.92/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.92/0.99      | u1_struct_0(sK0) != X0
% 1.92/0.99      | sK1 != sK1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_1911,c_972]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2454,plain,
% 1.92/0.99      ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | ~ v2_struct_0(k3_yellow19(sK0,u1_struct_0(sK0),sK1))
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_2453]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3334,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_3031,c_2454]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3483,plain,
% 1.92/0.99      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(subtyping,[status(esa)],[c_3334]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3650,plain,
% 1.92/0.99      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.92/0.99      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.92/0.99      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.92/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 1.92/0.99      inference(predicate_to_equality,[status(thm)],[c_3483]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_12,plain,
% 1.92/0.99      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.92/0.99      | v2_struct_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(X1)
% 1.92/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 1.92/0.99      inference(cnf_transformation,[],[f72]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_358,plain,
% 1.92/0.99      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.92/0.99      | v2_struct_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(X1)
% 1.92/0.99      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.92/0.99      | sK1 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_359,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.92/0.99      | v2_struct_0(X0)
% 1.92/0.99      | v1_xboole_0(sK1)
% 1.92/0.99      | ~ l1_struct_0(X0)
% 1.92/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_363,plain,
% 1.92/0.99      ( v2_struct_0(X0)
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.92/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.92/0.99      | ~ l1_struct_0(X0)
% 1.92/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(global_propositional_subsumption,[status(thm)],[c_359,c_20]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_364,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.92/0.99      | v2_struct_0(X0)
% 1.92/0.99      | ~ l1_struct_0(X0)
% 1.92/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_363]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_958,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.92/0.99      | v2_struct_0(X0)
% 1.92/0.99      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.92/0.99      | sK0 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_364,c_492]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_959,plain,
% 1.92/0.99      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.92/0.99      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.92/0.99      | v2_struct_0(sK0)
% 1.92/0.99      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_958]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_16,negated_conjecture,
% 1.92/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
% 1.92/0.99      inference(cnf_transformation,[],[f73]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_961,plain,
% 1.92/0.99      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(global_propositional_subsumption,
% 1.92/0.99                [status(thm)],
% 1.92/0.99                [c_959,c_23,c_18,c_17,c_16]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3438,plain,
% 1.92/0.99      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.92/0.99      inference(equality_resolution_simp,[status(thm)],[c_961]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3481,plain,
% 1.92/0.99      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.92/0.99      inference(subtyping,[status(esa)],[c_3438]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_0,plain,
% 1.92/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.92/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_987,plain,
% 1.92/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_492]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_988,plain,
% 1.92/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_987]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3486,plain,
% 1.92/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.92/0.99      inference(subtyping,[status(esa)],[c_988]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3697,plain,
% 1.92/0.99      ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.92/0.99      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.92/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.92/0.99      inference(light_normalisation,[status(thm)],[c_3650,c_3481,c_3486]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3698,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.92/0.99      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.92/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.92/0.99      inference(equality_resolution_simp,[status(thm)],[c_3697]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3488,negated_conjecture,
% 1.92/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
% 1.92/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3646,plain,
% 1.92/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
% 1.92/0.99      inference(predicate_to_equality,[status(thm)],[c_3488]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1,plain,
% 1.92/0.99      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.92/0.99      | ~ l1_struct_0(X0) ),
% 1.92/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_980,plain,
% 1.92/0.99      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK0 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_492]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_981,plain,
% 1.92/0.99      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_980]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3487,plain,
% 1.92/0.99      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.92/0.99      inference(subtyping,[status(esa)],[c_981]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3647,plain,
% 1.92/0.99      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.92/0.99      inference(predicate_to_equality,[status(thm)],[c_3487]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3657,plain,
% 1.92/0.99      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 1.92/0.99      inference(light_normalisation,[status(thm)],[c_3647,c_3486]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_14,negated_conjecture,
% 1.92/0.99      ( r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.92/0.99      inference(cnf_transformation,[],[f64]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_177,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.92/0.99      inference(prop_impl,[status(thm)],[c_14]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_11,plain,
% 1.92/0.99      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.92/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 1.92/0.99      | ~ l1_waybel_0(X1,X0)
% 1.92/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.92/0.99      | ~ v2_pre_topc(X0)
% 1.92/0.99      | ~ v7_waybel_0(X1)
% 1.92/0.99      | ~ v4_orders_2(X1)
% 1.92/0.99      | v2_struct_0(X0)
% 1.92/0.99      | v2_struct_0(X1)
% 1.92/0.99      | ~ l1_pre_topc(X0) ),
% 1.92/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_409,plain,
% 1.92/0.99      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.92/0.99      | ~ r3_waybel_9(X0,X1,X2)
% 1.92/0.99      | ~ l1_waybel_0(X1,X0)
% 1.92/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.92/0.99      | ~ v7_waybel_0(X1)
% 1.92/0.99      | ~ v4_orders_2(X1)
% 1.92/0.99      | v2_struct_0(X0)
% 1.92/0.99      | v2_struct_0(X1)
% 1.92/0.99      | ~ l1_pre_topc(X0)
% 1.92/0.99      | sK0 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_410,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.92/0.99      | ~ r3_waybel_9(sK0,X0,X1)
% 1.92/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.92/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.92/0.99      | ~ v7_waybel_0(X0)
% 1.92/0.99      | ~ v4_orders_2(X0)
% 1.92/0.99      | v2_struct_0(X0)
% 1.92/0.99      | v2_struct_0(sK0)
% 1.92/0.99      | ~ l1_pre_topc(sK0) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_409]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_414,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.92/0.99      | ~ r3_waybel_9(sK0,X0,X1)
% 1.92/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.92/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.92/0.99      | ~ v7_waybel_0(X0)
% 1.92/0.99      | ~ v4_orders_2(X0)
% 1.92/0.99      | v2_struct_0(X0) ),
% 1.92/0.99      inference(global_propositional_subsumption,
% 1.92/0.99                [status(thm)],
% 1.92/0.99                [c_410,c_23,c_21]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_794,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ l1_waybel_0(X0,sK0)
% 1.92/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.92/0.99      | ~ v7_waybel_0(X0)
% 1.92/0.99      | ~ v4_orders_2(X0)
% 1.92/0.99      | v2_struct_0(X0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 1.92/0.99      | sK2 != X1
% 1.92/0.99      | sK0 != sK0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_177,c_414]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_795,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.92/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_794]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_797,plain,
% 1.92/0.99      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.92/0.99      inference(global_propositional_subsumption,[status(thm)],[c_795,c_15]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_798,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_797]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_908,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(X2)
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(X2)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 1.92/0.99      | sK0 != X2 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_798]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_909,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(sK0)
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | ~ l1_struct_0(sK0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_908]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_913,plain,
% 1.92/0.99      ( v1_xboole_0(X0)
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.92/0.99      inference(global_propositional_subsumption,
% 1.92/0.99                [status(thm)],
% 1.92/0.99                [c_909,c_23,c_21,c_64]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_914,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_913]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1418,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.92/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X1)
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.92/0.99      | sK1 != X0 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_914,c_17]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1419,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | v1_xboole_0(sK1)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_1418]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1423,plain,
% 1.92/0.99      ( v1_xboole_0(X0)
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(global_propositional_subsumption,[status(thm)],[c_1419,c_20]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1424,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.92/0.99      inference(renaming,[status(thm)],[c_1423]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_1850,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v1_xboole_0(X0)
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.92/0.99      | sK1 != sK1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_1424]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2485,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.92/0.99      | u1_struct_0(sK0) != X0
% 1.92/0.99      | sK1 != sK1 ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_1850,c_972]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2486,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,u1_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(u1_struct_0(sK0))) ),
% 1.92/0.99      inference(unflattening,[status(thm)],[c_2485]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_2797,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_2486,c_2470]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3004,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.92/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_2797,c_2548]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3358,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(resolution_lifted,[status(thm)],[c_3004,c_2454]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3482,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2)
% 1.92/0.99      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.92/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0))))))
% 1.92/0.99      | k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.92/0.99      inference(subtyping,[status(esa)],[c_3358]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3651,plain,
% 1.92/0.99      ( k3_yellow19(sK0,u1_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(u1_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.92/0.99      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.92/0.99      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.92/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK0)))))) != iProver_top ),
% 1.92/0.99      inference(predicate_to_equality,[status(thm)],[c_3482]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3690,plain,
% 1.92/0.99      ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.92/0.99      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.92/0.99      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.92/0.99      | r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.92/0.99      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.92/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.92/0.99      inference(light_normalisation,[status(thm)],[c_3651,c_3481,c_3486]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3691,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.92/0.99      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.92/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top ),
% 1.92/0.99      inference(equality_resolution_simp,[status(thm)],[c_3690]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3695,plain,
% 1.92/0.99      ( r1_waybel_7(sK0,sK1,sK2) = iProver_top ),
% 1.92/0.99      inference(forward_subsumption_resolution,
% 1.92/0.99                [status(thm)],
% 1.92/0.99                [c_3691,c_3646,c_3657]) ).
% 1.92/0.99  
% 1.92/0.99  cnf(c_3702,plain,
% 1.92/0.99      ( $false ),
% 1.92/0.99      inference(forward_subsumption_resolution,
% 1.92/0.99                [status(thm)],
% 1.92/0.99                [c_3698,c_3646,c_3657,c_3695]) ).
% 1.92/0.99  
% 1.92/0.99  
% 1.92/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.92/0.99  
% 1.92/0.99  ------                               Statistics
% 1.92/0.99  
% 1.92/0.99  ------ General
% 1.92/0.99  
% 1.92/0.99  abstr_ref_over_cycles:                  0
% 1.92/0.99  abstr_ref_under_cycles:                 0
% 1.92/0.99  gc_basic_clause_elim:                   0
% 1.92/0.99  forced_gc_time:                         0
% 1.92/0.99  parsing_time:                           0.011
% 1.92/0.99  unif_index_cands_time:                  0.
% 1.92/0.99  unif_index_add_time:                    0.
% 1.92/0.99  orderings_time:                         0.
% 1.92/0.99  out_proof_time:                         0.016
% 1.92/0.99  total_time:                             0.161
% 1.92/0.99  num_of_symbols:                         56
% 1.92/0.99  num_of_terms:                           1624
% 1.92/0.99  
% 1.92/0.99  ------ Preprocessing
% 1.92/0.99  
% 1.92/0.99  num_of_splits:                          0
% 1.92/0.99  num_of_split_atoms:                     0
% 1.92/0.99  num_of_reused_defs:                     0
% 1.92/0.99  num_eq_ax_congr_red:                    3
% 1.92/0.99  num_of_sem_filtered_clauses:            1
% 1.92/0.99  num_of_subtypes:                        4
% 1.92/0.99  monotx_restored_types:                  0
% 1.92/0.99  sat_num_of_epr_types:                   0
% 1.92/0.99  sat_num_of_non_cyclic_types:            0
% 1.92/0.99  sat_guarded_non_collapsed_types:        0
% 1.92/0.99  num_pure_diseq_elim:                    0
% 1.92/0.99  simp_replaced_by:                       0
% 1.92/0.99  res_preprocessed:                       82
% 1.92/0.99  prep_upred:                             0
% 1.92/0.99  prep_unflattend:                        40
% 1.92/0.99  smt_new_axioms:                         0
% 1.92/0.99  pred_elim_cands:                        2
% 1.92/0.99  pred_elim:                              12
% 1.92/0.99  pred_elim_cl:                           13
% 1.92/0.99  pred_elim_cycles:                       24
% 1.92/0.99  merged_defs:                            2
% 1.92/0.99  merged_defs_ncl:                        0
% 1.92/0.99  bin_hyper_res:                          2
% 1.92/0.99  prep_cycles:                            4
% 1.92/0.99  pred_elim_time:                         0.097
% 1.92/0.99  splitting_time:                         0.
% 1.92/0.99  sem_filter_time:                        0.
% 1.92/0.99  monotx_time:                            0.
% 1.92/0.99  subtype_inf_time:                       0.
% 1.92/0.99  
% 1.92/0.99  ------ Problem properties
% 1.92/0.99  
% 1.92/0.99  clauses:                                9
% 1.92/0.99  conjectures:                            2
% 1.92/0.99  epr:                                    0
% 1.92/0.99  horn:                                   7
% 1.92/0.99  ground:                                 9
% 1.92/0.99  unary:                                  5
% 1.92/0.99  binary:                                 0
% 1.92/0.99  lits:                                   33
% 1.92/0.99  lits_eq:                                14
% 1.92/0.99  fd_pure:                                0
% 1.92/0.99  fd_pseudo:                              0
% 1.92/0.99  fd_cond:                                0
% 1.92/0.99  fd_pseudo_cond:                         0
% 1.92/0.99  ac_symbols:                             0
% 1.92/0.99  
% 1.92/0.99  ------ Propositional Solver
% 1.92/0.99  
% 1.92/0.99  prop_solver_calls:                      21
% 1.92/0.99  prop_fast_solver_calls:                 1616
% 1.92/0.99  smt_solver_calls:                       0
% 1.92/0.99  smt_fast_solver_calls:                  0
% 1.92/0.99  prop_num_of_clauses:                    432
% 1.92/0.99  prop_preprocess_simplified:             1791
% 1.92/0.99  prop_fo_subsumed:                       53
% 1.92/0.99  prop_solver_time:                       0.
% 1.92/0.99  smt_solver_time:                        0.
% 1.92/0.99  smt_fast_solver_time:                   0.
% 1.92/0.99  prop_fast_solver_time:                  0.
% 1.92/0.99  prop_unsat_core_time:                   0.
% 1.92/0.99  
% 1.92/0.99  ------ QBF
% 1.92/0.99  
% 1.92/0.99  qbf_q_res:                              0
% 1.92/0.99  qbf_num_tautologies:                    0
% 1.92/0.99  qbf_prep_cycles:                        0
% 1.92/0.99  
% 1.92/0.99  ------ BMC1
% 1.92/0.99  
% 1.92/0.99  bmc1_current_bound:                     -1
% 1.92/0.99  bmc1_last_solved_bound:                 -1
% 1.92/0.99  bmc1_unsat_core_size:                   -1
% 1.92/0.99  bmc1_unsat_core_parents_size:           -1
% 1.92/0.99  bmc1_merge_next_fun:                    0
% 1.92/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.92/0.99  
% 1.92/0.99  ------ Instantiation
% 1.92/0.99  
% 1.92/0.99  inst_num_of_clauses:                    25
% 1.92/0.99  inst_num_in_passive:                    0
% 1.92/0.99  inst_num_in_active:                     0
% 1.92/0.99  inst_num_in_unprocessed:                25
% 1.92/0.99  inst_num_of_loops:                      0
% 1.92/0.99  inst_num_of_learning_restarts:          0
% 1.92/0.99  inst_num_moves_active_passive:          0
% 1.92/0.99  inst_lit_activity:                      0
% 1.92/0.99  inst_lit_activity_moves:                0
% 1.92/0.99  inst_num_tautologies:                   0
% 1.92/0.99  inst_num_prop_implied:                  0
% 1.92/0.99  inst_num_existing_simplified:           0
% 1.92/0.99  inst_num_eq_res_simplified:             0
% 1.92/0.99  inst_num_child_elim:                    0
% 1.92/0.99  inst_num_of_dismatching_blockings:      0
% 1.92/0.99  inst_num_of_non_proper_insts:           0
% 1.92/0.99  inst_num_of_duplicates:                 0
% 1.92/0.99  inst_inst_num_from_inst_to_res:         0
% 1.92/0.99  inst_dismatching_checking_time:         0.
% 1.92/0.99  
% 1.92/0.99  ------ Resolution
% 1.92/0.99  
% 1.92/0.99  res_num_of_clauses:                     0
% 1.92/0.99  res_num_in_passive:                     0
% 1.92/0.99  res_num_in_active:                      0
% 1.92/0.99  res_num_of_loops:                       86
% 1.92/0.99  res_forward_subset_subsumed:            0
% 1.92/0.99  res_backward_subset_subsumed:           0
% 1.92/0.99  res_forward_subsumed:                   6
% 1.92/0.99  res_backward_subsumed:                  10
% 1.92/0.99  res_forward_subsumption_resolution:     2
% 1.92/0.99  res_backward_subsumption_resolution:    0
% 1.92/0.99  res_clause_to_clause_subsumption:       224
% 1.92/0.99  res_orphan_elimination:                 0
% 1.92/0.99  res_tautology_del:                      6
% 1.92/0.99  res_num_eq_res_simplified:              1
% 1.92/0.99  res_num_sel_changes:                    0
% 1.92/0.99  res_moves_from_active_to_pass:          0
% 1.92/0.99  
% 1.92/0.99  ------ Superposition
% 1.92/0.99  
% 1.92/0.99  sup_time_total:                         0.
% 1.92/0.99  sup_time_generating:                    0.
% 1.92/0.99  sup_time_sim_full:                      0.
% 1.92/0.99  sup_time_sim_immed:                     0.
% 1.92/0.99  
% 1.92/0.99  sup_num_of_clauses:                     0
% 1.92/0.99  sup_num_in_active:                      0
% 1.92/0.99  sup_num_in_passive:                     0
% 1.92/0.99  sup_num_of_loops:                       0
% 1.92/0.99  sup_fw_superposition:                   0
% 1.92/0.99  sup_bw_superposition:                   0
% 1.92/0.99  sup_immediate_simplified:               0
% 1.92/0.99  sup_given_eliminated:                   0
% 1.92/0.99  comparisons_done:                       0
% 1.92/0.99  comparisons_avoided:                    0
% 1.92/0.99  
% 1.92/0.99  ------ Simplifications
% 1.92/0.99  
% 1.92/0.99  
% 1.92/0.99  sim_fw_subset_subsumed:                 0
% 1.92/0.99  sim_bw_subset_subsumed:                 0
% 1.92/0.99  sim_fw_subsumed:                        0
% 1.92/0.99  sim_bw_subsumed:                        1
% 1.92/0.99  sim_fw_subsumption_res:                 6
% 1.92/0.99  sim_bw_subsumption_res:                 0
% 1.92/0.99  sim_tautology_del:                      0
% 1.92/0.99  sim_eq_tautology_del:                   0
% 1.92/0.99  sim_eq_res_simp:                        2
% 1.92/0.99  sim_fw_demodulated:                     0
% 1.92/0.99  sim_bw_demodulated:                     0
% 1.92/0.99  sim_light_normalised:                   6
% 1.92/0.99  sim_joinable_taut:                      0
% 1.92/0.99  sim_joinable_simp:                      0
% 1.92/0.99  sim_ac_normalised:                      0
% 1.92/0.99  sim_smt_subsumption:                    0
% 1.92/0.99  
%------------------------------------------------------------------------------
