%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:20 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  218 (1684 expanded)
%              Number of clauses        :  136 ( 331 expanded)
%              Number of leaves         :   17 ( 482 expanded)
%              Depth                    :   28
%              Number of atoms          : 1376 (15244 expanded)
%              Number of equality atoms :  238 ( 562 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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
             => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
               => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
                <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_waybel_7(X0,X1,X2)
            | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
          & ( r2_waybel_7(X0,X1,X2)
            | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r2_waybel_7(X0,X1,sK2)
          | ~ r2_hidden(sK2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
        & ( r2_waybel_7(X0,X1,sK2)
          | r2_hidden(sK2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & ( r2_waybel_7(X0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ( ~ r2_waybel_7(X0,sK1,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))) )
            & ( r2_waybel_7(X0,sK1,X2)
              | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK1))) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_waybel_7(X0,X1,X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
                & ( r2_waybel_7(X0,X1,X2)
                  | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
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
              ( ( ~ r2_waybel_7(sK0,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
              & ( r2_waybel_7(sK0,X1,X2)
                | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1))) )
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

fof(f45,plain,
    ( ( ~ r2_waybel_7(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    & ( r2_waybel_7(sK0,sK1,sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43,f42])).

fof(f68,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f83,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f68,f53])).

fof(f69,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f69,f53])).

fof(f11,axiom,(
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
    inference(pure_predicate_removal,[],[f11])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
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
    inference(definition_unfolding,[],[f59,f53,f53,f53,f53])).

fof(f67,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f67,f53])).

fof(f66,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
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
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f19,plain,(
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
    inference(pure_predicate_removal,[],[f16])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
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
    inference(definition_unfolding,[],[f57,f53,f53,f53])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
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
    inference(definition_unfolding,[],[f58,f53,f53,f53,f53])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
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
    inference(definition_unfolding,[],[f56,f53,f53,f53])).

fof(f73,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
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
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
                  | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
                & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

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
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
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
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
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
    inference(definition_unfolding,[],[f55,f53,f53,f53])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f62,f53,f53,f53,f53])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f70,f53])).

fof(f72,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

cnf(c_21,negated_conjecture,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_20,negated_conjecture,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f78])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_355,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_356,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_360,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_23])).

cnf(c_361,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_1363,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_361])).

cnf(c_1756,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1363])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_569,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_570,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_2122,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1756,c_570])).

cnf(c_2123,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_2122])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2127,plain,
    ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2123,c_26])).

cnf(c_2128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_2127])).

cnf(c_9,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1284,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_1285,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1284])).

cnf(c_1289,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1285,c_23])).

cnf(c_1290,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1289])).

cnf(c_1817,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1290])).

cnf(c_2095,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1817,c_570])).

cnf(c_2096,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2095])).

cnf(c_2100,plain,
    ( v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2096,c_26])).

cnf(c_2101,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2100])).

cnf(c_12,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_10,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_149,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_10])).

cnf(c_150,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_149])).

cnf(c_1248,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_150,c_20])).

cnf(c_1249,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1248])).

cnf(c_1253,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1249,c_23])).

cnf(c_1254,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1253])).

cnf(c_1846,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1254])).

cnf(c_2068,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1846,c_570])).

cnf(c_2069,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_2068])).

cnf(c_2073,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2069,c_26])).

cnf(c_2074,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_2073])).

cnf(c_16,negated_conjecture,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_193,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_445,plain,
    ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_446,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_450,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_446,c_26,c_24])).

cnf(c_905,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK0,X0) != sK1
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_193,c_450])).

cnf(c_906,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK0,X0) != sK1 ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_910,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK0,X0) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_906,c_18])).

cnf(c_911,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK0,X0) != sK1 ),
    inference(renaming,[status(thm)],[c_910])).

cnf(c_7,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1327,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_1328,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1327])).

cnf(c_1332,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1328,c_23])).

cnf(c_1333,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1332])).

cnf(c_1788,plain,
    ( l1_waybel_0(k3_yellow19(X0,X1,sK1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1333])).

cnf(c_1946,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | k3_yellow19(X2,X1,sK1) != X0
    | k2_yellow19(sK0,X0) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != sK1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_911,c_1788])).

cnf(c_1947,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1946])).

cnf(c_70,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1951,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1947,c_26,c_24,c_70])).

cnf(c_2158,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2074,c_1951])).

cnf(c_2173,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2101,c_2158])).

cnf(c_2190,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_2128,c_2173])).

cnf(c_2829,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))) != iProver_top
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2190])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2063,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_570])).

cnf(c_2064,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_2063])).

cnf(c_2886,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))) != iProver_top
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2829,c_2064])).

cnf(c_3065,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2886])).

cnf(c_15,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_394,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_22])).

cnf(c_395,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK1)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_399,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_23])).

cnf(c_400,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(renaming,[status(thm)],[c_399])).

cnf(c_1398,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_400])).

cnf(c_1875,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1398])).

cnf(c_2052,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != sK1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1875,c_570])).

cnf(c_2053,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_2052])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_402,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_400])).

cnf(c_2055,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2053,c_26,c_24,c_21,c_20,c_19,c_70,c_402])).

cnf(c_2425,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_2055])).

cnf(c_3066,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | sK1 != sK1
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3065,c_2425])).

cnf(c_3067,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3066])).

cnf(c_34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_17,negated_conjecture,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_195,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_478,plain,
    ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ l1_waybel_0(X1,X0)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_479,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ l1_waybel_0(X0,sK0)
    | r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_483,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ l1_waybel_0(X0,sK0)
    | r2_hidden(X1,k10_yellow_6(sK0,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_26,c_24])).

cnf(c_872,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | r2_hidden(X1,k10_yellow_6(sK0,X0))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK0,X0) != sK1
    | sK2 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_195,c_483])).

cnf(c_873,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | r2_hidden(sK2,k10_yellow_6(sK0,X0))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK0,X0) != sK1 ),
    inference(unflattening,[status(thm)],[c_872])).

cnf(c_877,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_hidden(sK2,k10_yellow_6(sK0,X0))
    | ~ l1_waybel_0(X0,sK0)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK0,X0) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_873,c_18])).

cnf(c_878,plain,
    ( ~ l1_waybel_0(X0,sK0)
    | r2_hidden(sK2,k10_yellow_6(sK0,X0))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow19(sK0,X0) != sK1 ),
    inference(renaming,[status(thm)],[c_877])).

cnf(c_1988,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,X0))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | k3_yellow19(X2,X1,sK1) != X0
    | k2_yellow19(sK0,X0) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != sK1
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_878,c_1788])).

cnf(c_1989,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1988])).

cnf(c_1993,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1989,c_26,c_24,c_70])).

cnf(c_2159,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2074,c_1993])).

cnf(c_2172,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2101,c_2159])).

cnf(c_2219,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(resolution,[status(thm)],[c_2128,c_2172])).

cnf(c_2828,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))) = iProver_top
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2219])).

cnf(c_2869,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))) = iProver_top
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2828,c_2064])).

cnf(c_3319,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != sK1
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2869])).

cnf(c_3320,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | sK1 != sK1
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3319,c_2425])).

cnf(c_3321,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3320])).

cnf(c_2834,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2843,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2834,c_2064])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_connsp_2(X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_511,plain,
    ( r2_hidden(X0,k1_connsp_2(X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_512,plain,
    ( r2_hidden(X0,k1_connsp_2(sK0,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_516,plain,
    ( r2_hidden(X0,k1_connsp_2(sK0,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_26,c_24])).

cnf(c_2831,plain,
    ( r2_hidden(X0,k1_connsp_2(sK0,X0)) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_2853,plain,
    ( r2_hidden(X0,k1_connsp_2(sK0,X0)) = iProver_top
    | m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2831,c_2064])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_529,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_26,c_24])).

cnf(c_2830,plain,
    ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_2858,plain,
    ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2830,c_2064])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2835,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3158,plain,
    ( r2_hidden(X0,k1_connsp_2(sK0,X1)) != iProver_top
    | m1_subset_1(X1,k2_struct_0(sK0)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2858,c_2835])).

cnf(c_3473,plain,
    ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2853,c_3158])).

cnf(c_3480,plain,
    ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2843,c_3473])).

cnf(c_3536,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3067,c_34,c_3321,c_3480])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2836,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2846,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2836,c_0])).

cnf(c_3541,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3536,c_2846])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.99/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.00  
% 1.99/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/1.00  
% 1.99/1.00  ------  iProver source info
% 1.99/1.00  
% 1.99/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.99/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/1.00  git: non_committed_changes: false
% 1.99/1.00  git: last_make_outside_of_git: false
% 1.99/1.00  
% 1.99/1.00  ------ 
% 1.99/1.00  
% 1.99/1.00  ------ Input Options
% 1.99/1.00  
% 1.99/1.00  --out_options                           all
% 1.99/1.00  --tptp_safe_out                         true
% 1.99/1.00  --problem_path                          ""
% 1.99/1.00  --include_path                          ""
% 1.99/1.00  --clausifier                            res/vclausify_rel
% 1.99/1.00  --clausifier_options                    --mode clausify
% 1.99/1.00  --stdin                                 false
% 1.99/1.00  --stats_out                             all
% 1.99/1.00  
% 1.99/1.00  ------ General Options
% 1.99/1.00  
% 1.99/1.00  --fof                                   false
% 1.99/1.00  --time_out_real                         305.
% 1.99/1.00  --time_out_virtual                      -1.
% 1.99/1.00  --symbol_type_check                     false
% 1.99/1.00  --clausify_out                          false
% 1.99/1.00  --sig_cnt_out                           false
% 1.99/1.00  --trig_cnt_out                          false
% 1.99/1.00  --trig_cnt_out_tolerance                1.
% 1.99/1.00  --trig_cnt_out_sk_spl                   false
% 1.99/1.00  --abstr_cl_out                          false
% 1.99/1.00  
% 1.99/1.00  ------ Global Options
% 1.99/1.00  
% 1.99/1.00  --schedule                              default
% 1.99/1.00  --add_important_lit                     false
% 1.99/1.00  --prop_solver_per_cl                    1000
% 1.99/1.00  --min_unsat_core                        false
% 1.99/1.00  --soft_assumptions                      false
% 1.99/1.00  --soft_lemma_size                       3
% 1.99/1.00  --prop_impl_unit_size                   0
% 1.99/1.00  --prop_impl_unit                        []
% 1.99/1.00  --share_sel_clauses                     true
% 1.99/1.00  --reset_solvers                         false
% 1.99/1.00  --bc_imp_inh                            [conj_cone]
% 1.99/1.00  --conj_cone_tolerance                   3.
% 1.99/1.00  --extra_neg_conj                        none
% 1.99/1.00  --large_theory_mode                     true
% 1.99/1.00  --prolific_symb_bound                   200
% 1.99/1.00  --lt_threshold                          2000
% 1.99/1.00  --clause_weak_htbl                      true
% 1.99/1.00  --gc_record_bc_elim                     false
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing Options
% 1.99/1.00  
% 1.99/1.00  --preprocessing_flag                    true
% 1.99/1.00  --time_out_prep_mult                    0.1
% 1.99/1.00  --splitting_mode                        input
% 1.99/1.00  --splitting_grd                         true
% 1.99/1.00  --splitting_cvd                         false
% 1.99/1.00  --splitting_cvd_svl                     false
% 1.99/1.00  --splitting_nvd                         32
% 1.99/1.00  --sub_typing                            true
% 1.99/1.00  --prep_gs_sim                           true
% 1.99/1.00  --prep_unflatten                        true
% 1.99/1.00  --prep_res_sim                          true
% 1.99/1.00  --prep_upred                            true
% 1.99/1.00  --prep_sem_filter                       exhaustive
% 1.99/1.00  --prep_sem_filter_out                   false
% 1.99/1.00  --pred_elim                             true
% 1.99/1.00  --res_sim_input                         true
% 1.99/1.00  --eq_ax_congr_red                       true
% 1.99/1.00  --pure_diseq_elim                       true
% 1.99/1.00  --brand_transform                       false
% 1.99/1.00  --non_eq_to_eq                          false
% 1.99/1.00  --prep_def_merge                        true
% 1.99/1.00  --prep_def_merge_prop_impl              false
% 1.99/1.00  --prep_def_merge_mbd                    true
% 1.99/1.00  --prep_def_merge_tr_red                 false
% 1.99/1.00  --prep_def_merge_tr_cl                  false
% 1.99/1.00  --smt_preprocessing                     true
% 1.99/1.00  --smt_ac_axioms                         fast
% 1.99/1.00  --preprocessed_out                      false
% 1.99/1.00  --preprocessed_stats                    false
% 1.99/1.00  
% 1.99/1.00  ------ Abstraction refinement Options
% 1.99/1.00  
% 1.99/1.00  --abstr_ref                             []
% 1.99/1.00  --abstr_ref_prep                        false
% 1.99/1.00  --abstr_ref_until_sat                   false
% 1.99/1.00  --abstr_ref_sig_restrict                funpre
% 1.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/1.00  --abstr_ref_under                       []
% 1.99/1.00  
% 1.99/1.00  ------ SAT Options
% 1.99/1.00  
% 1.99/1.00  --sat_mode                              false
% 1.99/1.00  --sat_fm_restart_options                ""
% 1.99/1.00  --sat_gr_def                            false
% 1.99/1.00  --sat_epr_types                         true
% 1.99/1.00  --sat_non_cyclic_types                  false
% 1.99/1.00  --sat_finite_models                     false
% 1.99/1.00  --sat_fm_lemmas                         false
% 1.99/1.00  --sat_fm_prep                           false
% 1.99/1.00  --sat_fm_uc_incr                        true
% 1.99/1.00  --sat_out_model                         small
% 1.99/1.00  --sat_out_clauses                       false
% 1.99/1.00  
% 1.99/1.00  ------ QBF Options
% 1.99/1.00  
% 1.99/1.00  --qbf_mode                              false
% 1.99/1.00  --qbf_elim_univ                         false
% 1.99/1.00  --qbf_dom_inst                          none
% 1.99/1.00  --qbf_dom_pre_inst                      false
% 1.99/1.00  --qbf_sk_in                             false
% 1.99/1.00  --qbf_pred_elim                         true
% 1.99/1.00  --qbf_split                             512
% 1.99/1.00  
% 1.99/1.00  ------ BMC1 Options
% 1.99/1.00  
% 1.99/1.00  --bmc1_incremental                      false
% 1.99/1.00  --bmc1_axioms                           reachable_all
% 1.99/1.00  --bmc1_min_bound                        0
% 1.99/1.00  --bmc1_max_bound                        -1
% 1.99/1.00  --bmc1_max_bound_default                -1
% 1.99/1.00  --bmc1_symbol_reachability              true
% 1.99/1.00  --bmc1_property_lemmas                  false
% 1.99/1.00  --bmc1_k_induction                      false
% 1.99/1.00  --bmc1_non_equiv_states                 false
% 1.99/1.00  --bmc1_deadlock                         false
% 1.99/1.00  --bmc1_ucm                              false
% 1.99/1.00  --bmc1_add_unsat_core                   none
% 1.99/1.00  --bmc1_unsat_core_children              false
% 1.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/1.00  --bmc1_out_stat                         full
% 1.99/1.00  --bmc1_ground_init                      false
% 1.99/1.00  --bmc1_pre_inst_next_state              false
% 1.99/1.00  --bmc1_pre_inst_state                   false
% 1.99/1.00  --bmc1_pre_inst_reach_state             false
% 1.99/1.00  --bmc1_out_unsat_core                   false
% 1.99/1.00  --bmc1_aig_witness_out                  false
% 1.99/1.00  --bmc1_verbose                          false
% 1.99/1.00  --bmc1_dump_clauses_tptp                false
% 1.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.99/1.00  --bmc1_dump_file                        -
% 1.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.99/1.00  --bmc1_ucm_extend_mode                  1
% 1.99/1.00  --bmc1_ucm_init_mode                    2
% 1.99/1.00  --bmc1_ucm_cone_mode                    none
% 1.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.99/1.00  --bmc1_ucm_relax_model                  4
% 1.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/1.00  --bmc1_ucm_layered_model                none
% 1.99/1.00  --bmc1_ucm_max_lemma_size               10
% 1.99/1.00  
% 1.99/1.00  ------ AIG Options
% 1.99/1.00  
% 1.99/1.00  --aig_mode                              false
% 1.99/1.00  
% 1.99/1.00  ------ Instantiation Options
% 1.99/1.00  
% 1.99/1.00  --instantiation_flag                    true
% 1.99/1.00  --inst_sos_flag                         false
% 1.99/1.00  --inst_sos_phase                        true
% 1.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/1.00  --inst_lit_sel_side                     num_symb
% 1.99/1.00  --inst_solver_per_active                1400
% 1.99/1.00  --inst_solver_calls_frac                1.
% 1.99/1.00  --inst_passive_queue_type               priority_queues
% 1.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.00  --inst_passive_queues_freq              [25;2]
% 1.99/1.00  --inst_dismatching                      true
% 1.99/1.00  --inst_eager_unprocessed_to_passive     true
% 1.99/1.00  --inst_prop_sim_given                   true
% 1.99/1.00  --inst_prop_sim_new                     false
% 1.99/1.00  --inst_subs_new                         false
% 1.99/1.00  --inst_eq_res_simp                      false
% 1.99/1.00  --inst_subs_given                       false
% 1.99/1.00  --inst_orphan_elimination               true
% 1.99/1.00  --inst_learning_loop_flag               true
% 1.99/1.00  --inst_learning_start                   3000
% 1.99/1.00  --inst_learning_factor                  2
% 1.99/1.00  --inst_start_prop_sim_after_learn       3
% 1.99/1.00  --inst_sel_renew                        solver
% 1.99/1.00  --inst_lit_activity_flag                true
% 1.99/1.00  --inst_restr_to_given                   false
% 1.99/1.00  --inst_activity_threshold               500
% 1.99/1.00  --inst_out_proof                        true
% 1.99/1.00  
% 1.99/1.00  ------ Resolution Options
% 1.99/1.00  
% 1.99/1.00  --resolution_flag                       true
% 1.99/1.00  --res_lit_sel                           adaptive
% 1.99/1.00  --res_lit_sel_side                      none
% 1.99/1.00  --res_ordering                          kbo
% 1.99/1.00  --res_to_prop_solver                    active
% 1.99/1.00  --res_prop_simpl_new                    false
% 1.99/1.00  --res_prop_simpl_given                  true
% 1.99/1.00  --res_passive_queue_type                priority_queues
% 1.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.00  --res_passive_queues_freq               [15;5]
% 1.99/1.00  --res_forward_subs                      full
% 1.99/1.00  --res_backward_subs                     full
% 1.99/1.00  --res_forward_subs_resolution           true
% 1.99/1.00  --res_backward_subs_resolution          true
% 1.99/1.00  --res_orphan_elimination                true
% 1.99/1.00  --res_time_limit                        2.
% 1.99/1.00  --res_out_proof                         true
% 1.99/1.00  
% 1.99/1.00  ------ Superposition Options
% 1.99/1.00  
% 1.99/1.00  --superposition_flag                    true
% 1.99/1.00  --sup_passive_queue_type                priority_queues
% 1.99/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.00  --demod_completeness_check              fast
% 1.99/1.00  --demod_use_ground                      true
% 1.99/1.00  --sup_to_prop_solver                    passive
% 1.99/1.00  --sup_prop_simpl_new                    true
% 1.99/1.00  --sup_prop_simpl_given                  true
% 1.99/1.00  --sup_fun_splitting                     false
% 1.99/1.00  --sup_smt_interval                      50000
% 1.99/1.00  
% 1.99/1.00  ------ Superposition Simplification Setup
% 1.99/1.00  
% 1.99/1.00  --sup_indices_passive                   []
% 1.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_full_bw                           [BwDemod]
% 1.99/1.00  --sup_immed_triv                        [TrivRules]
% 1.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_immed_bw_main                     []
% 1.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.00  
% 1.99/1.00  ------ Combination Options
% 1.99/1.00  
% 1.99/1.00  --comb_res_mult                         3
% 1.99/1.00  --comb_sup_mult                         2
% 1.99/1.00  --comb_inst_mult                        10
% 1.99/1.00  
% 1.99/1.00  ------ Debug Options
% 1.99/1.00  
% 1.99/1.00  --dbg_backtrace                         false
% 1.99/1.00  --dbg_dump_prop_clauses                 false
% 1.99/1.00  --dbg_dump_prop_clauses_file            -
% 1.99/1.00  --dbg_out_stat                          false
% 1.99/1.00  ------ Parsing...
% 1.99/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/1.00  ------ Proving...
% 1.99/1.00  ------ Problem Properties 
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  clauses                                 12
% 1.99/1.00  conjectures                             3
% 1.99/1.00  EPR                                     1
% 1.99/1.00  Horn                                    11
% 1.99/1.00  unary                                   7
% 1.99/1.00  binary                                  2
% 1.99/1.00  lits                                    30
% 1.99/1.00  lits eq                                 9
% 1.99/1.00  fd_pure                                 0
% 1.99/1.00  fd_pseudo                               0
% 1.99/1.00  fd_cond                                 0
% 1.99/1.00  fd_pseudo_cond                          0
% 1.99/1.00  AC symbols                              0
% 1.99/1.00  
% 1.99/1.00  ------ Schedule dynamic 5 is on 
% 1.99/1.00  
% 1.99/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  ------ 
% 1.99/1.00  Current options:
% 1.99/1.00  ------ 
% 1.99/1.00  
% 1.99/1.00  ------ Input Options
% 1.99/1.00  
% 1.99/1.00  --out_options                           all
% 1.99/1.00  --tptp_safe_out                         true
% 1.99/1.00  --problem_path                          ""
% 1.99/1.00  --include_path                          ""
% 1.99/1.00  --clausifier                            res/vclausify_rel
% 1.99/1.00  --clausifier_options                    --mode clausify
% 1.99/1.00  --stdin                                 false
% 1.99/1.00  --stats_out                             all
% 1.99/1.00  
% 1.99/1.00  ------ General Options
% 1.99/1.00  
% 1.99/1.00  --fof                                   false
% 1.99/1.00  --time_out_real                         305.
% 1.99/1.00  --time_out_virtual                      -1.
% 1.99/1.00  --symbol_type_check                     false
% 1.99/1.00  --clausify_out                          false
% 1.99/1.00  --sig_cnt_out                           false
% 1.99/1.00  --trig_cnt_out                          false
% 1.99/1.00  --trig_cnt_out_tolerance                1.
% 1.99/1.00  --trig_cnt_out_sk_spl                   false
% 1.99/1.00  --abstr_cl_out                          false
% 1.99/1.00  
% 1.99/1.00  ------ Global Options
% 1.99/1.00  
% 1.99/1.00  --schedule                              default
% 1.99/1.00  --add_important_lit                     false
% 1.99/1.00  --prop_solver_per_cl                    1000
% 1.99/1.00  --min_unsat_core                        false
% 1.99/1.00  --soft_assumptions                      false
% 1.99/1.00  --soft_lemma_size                       3
% 1.99/1.00  --prop_impl_unit_size                   0
% 1.99/1.00  --prop_impl_unit                        []
% 1.99/1.00  --share_sel_clauses                     true
% 1.99/1.00  --reset_solvers                         false
% 1.99/1.00  --bc_imp_inh                            [conj_cone]
% 1.99/1.00  --conj_cone_tolerance                   3.
% 1.99/1.00  --extra_neg_conj                        none
% 1.99/1.00  --large_theory_mode                     true
% 1.99/1.00  --prolific_symb_bound                   200
% 1.99/1.00  --lt_threshold                          2000
% 1.99/1.00  --clause_weak_htbl                      true
% 1.99/1.00  --gc_record_bc_elim                     false
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing Options
% 1.99/1.00  
% 1.99/1.00  --preprocessing_flag                    true
% 1.99/1.00  --time_out_prep_mult                    0.1
% 1.99/1.00  --splitting_mode                        input
% 1.99/1.00  --splitting_grd                         true
% 1.99/1.00  --splitting_cvd                         false
% 1.99/1.00  --splitting_cvd_svl                     false
% 1.99/1.00  --splitting_nvd                         32
% 1.99/1.00  --sub_typing                            true
% 1.99/1.00  --prep_gs_sim                           true
% 1.99/1.00  --prep_unflatten                        true
% 1.99/1.00  --prep_res_sim                          true
% 1.99/1.00  --prep_upred                            true
% 1.99/1.00  --prep_sem_filter                       exhaustive
% 1.99/1.00  --prep_sem_filter_out                   false
% 1.99/1.00  --pred_elim                             true
% 1.99/1.00  --res_sim_input                         true
% 1.99/1.00  --eq_ax_congr_red                       true
% 1.99/1.00  --pure_diseq_elim                       true
% 1.99/1.00  --brand_transform                       false
% 1.99/1.00  --non_eq_to_eq                          false
% 1.99/1.00  --prep_def_merge                        true
% 1.99/1.00  --prep_def_merge_prop_impl              false
% 1.99/1.00  --prep_def_merge_mbd                    true
% 1.99/1.00  --prep_def_merge_tr_red                 false
% 1.99/1.00  --prep_def_merge_tr_cl                  false
% 1.99/1.00  --smt_preprocessing                     true
% 1.99/1.00  --smt_ac_axioms                         fast
% 1.99/1.00  --preprocessed_out                      false
% 1.99/1.00  --preprocessed_stats                    false
% 1.99/1.00  
% 1.99/1.00  ------ Abstraction refinement Options
% 1.99/1.00  
% 1.99/1.00  --abstr_ref                             []
% 1.99/1.00  --abstr_ref_prep                        false
% 1.99/1.00  --abstr_ref_until_sat                   false
% 1.99/1.00  --abstr_ref_sig_restrict                funpre
% 1.99/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/1.00  --abstr_ref_under                       []
% 1.99/1.00  
% 1.99/1.00  ------ SAT Options
% 1.99/1.00  
% 1.99/1.00  --sat_mode                              false
% 1.99/1.00  --sat_fm_restart_options                ""
% 1.99/1.00  --sat_gr_def                            false
% 1.99/1.00  --sat_epr_types                         true
% 1.99/1.00  --sat_non_cyclic_types                  false
% 1.99/1.00  --sat_finite_models                     false
% 1.99/1.00  --sat_fm_lemmas                         false
% 1.99/1.00  --sat_fm_prep                           false
% 1.99/1.00  --sat_fm_uc_incr                        true
% 1.99/1.00  --sat_out_model                         small
% 1.99/1.00  --sat_out_clauses                       false
% 1.99/1.00  
% 1.99/1.00  ------ QBF Options
% 1.99/1.00  
% 1.99/1.00  --qbf_mode                              false
% 1.99/1.00  --qbf_elim_univ                         false
% 1.99/1.00  --qbf_dom_inst                          none
% 1.99/1.00  --qbf_dom_pre_inst                      false
% 1.99/1.00  --qbf_sk_in                             false
% 1.99/1.00  --qbf_pred_elim                         true
% 1.99/1.00  --qbf_split                             512
% 1.99/1.00  
% 1.99/1.00  ------ BMC1 Options
% 1.99/1.00  
% 1.99/1.00  --bmc1_incremental                      false
% 1.99/1.00  --bmc1_axioms                           reachable_all
% 1.99/1.00  --bmc1_min_bound                        0
% 1.99/1.00  --bmc1_max_bound                        -1
% 1.99/1.00  --bmc1_max_bound_default                -1
% 1.99/1.00  --bmc1_symbol_reachability              true
% 1.99/1.00  --bmc1_property_lemmas                  false
% 1.99/1.00  --bmc1_k_induction                      false
% 1.99/1.00  --bmc1_non_equiv_states                 false
% 1.99/1.00  --bmc1_deadlock                         false
% 1.99/1.00  --bmc1_ucm                              false
% 1.99/1.00  --bmc1_add_unsat_core                   none
% 1.99/1.00  --bmc1_unsat_core_children              false
% 1.99/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/1.00  --bmc1_out_stat                         full
% 1.99/1.00  --bmc1_ground_init                      false
% 1.99/1.00  --bmc1_pre_inst_next_state              false
% 1.99/1.00  --bmc1_pre_inst_state                   false
% 1.99/1.00  --bmc1_pre_inst_reach_state             false
% 1.99/1.00  --bmc1_out_unsat_core                   false
% 1.99/1.00  --bmc1_aig_witness_out                  false
% 1.99/1.00  --bmc1_verbose                          false
% 1.99/1.00  --bmc1_dump_clauses_tptp                false
% 1.99/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.99/1.00  --bmc1_dump_file                        -
% 1.99/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.99/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.99/1.00  --bmc1_ucm_extend_mode                  1
% 1.99/1.00  --bmc1_ucm_init_mode                    2
% 1.99/1.00  --bmc1_ucm_cone_mode                    none
% 1.99/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.99/1.00  --bmc1_ucm_relax_model                  4
% 1.99/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.99/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/1.00  --bmc1_ucm_layered_model                none
% 1.99/1.00  --bmc1_ucm_max_lemma_size               10
% 1.99/1.00  
% 1.99/1.00  ------ AIG Options
% 1.99/1.00  
% 1.99/1.00  --aig_mode                              false
% 1.99/1.00  
% 1.99/1.00  ------ Instantiation Options
% 1.99/1.00  
% 1.99/1.00  --instantiation_flag                    true
% 1.99/1.00  --inst_sos_flag                         false
% 1.99/1.00  --inst_sos_phase                        true
% 1.99/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/1.00  --inst_lit_sel_side                     none
% 1.99/1.00  --inst_solver_per_active                1400
% 1.99/1.00  --inst_solver_calls_frac                1.
% 1.99/1.00  --inst_passive_queue_type               priority_queues
% 1.99/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.01  --inst_passive_queues_freq              [25;2]
% 1.99/1.01  --inst_dismatching                      true
% 1.99/1.01  --inst_eager_unprocessed_to_passive     true
% 1.99/1.01  --inst_prop_sim_given                   true
% 1.99/1.01  --inst_prop_sim_new                     false
% 1.99/1.01  --inst_subs_new                         false
% 1.99/1.01  --inst_eq_res_simp                      false
% 1.99/1.01  --inst_subs_given                       false
% 1.99/1.01  --inst_orphan_elimination               true
% 1.99/1.01  --inst_learning_loop_flag               true
% 1.99/1.01  --inst_learning_start                   3000
% 1.99/1.01  --inst_learning_factor                  2
% 1.99/1.01  --inst_start_prop_sim_after_learn       3
% 1.99/1.01  --inst_sel_renew                        solver
% 1.99/1.01  --inst_lit_activity_flag                true
% 1.99/1.01  --inst_restr_to_given                   false
% 1.99/1.01  --inst_activity_threshold               500
% 1.99/1.01  --inst_out_proof                        true
% 1.99/1.01  
% 1.99/1.01  ------ Resolution Options
% 1.99/1.01  
% 1.99/1.01  --resolution_flag                       false
% 1.99/1.01  --res_lit_sel                           adaptive
% 1.99/1.01  --res_lit_sel_side                      none
% 1.99/1.01  --res_ordering                          kbo
% 1.99/1.01  --res_to_prop_solver                    active
% 1.99/1.01  --res_prop_simpl_new                    false
% 1.99/1.01  --res_prop_simpl_given                  true
% 1.99/1.01  --res_passive_queue_type                priority_queues
% 1.99/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.01  --res_passive_queues_freq               [15;5]
% 1.99/1.01  --res_forward_subs                      full
% 1.99/1.01  --res_backward_subs                     full
% 1.99/1.01  --res_forward_subs_resolution           true
% 1.99/1.01  --res_backward_subs_resolution          true
% 1.99/1.01  --res_orphan_elimination                true
% 1.99/1.01  --res_time_limit                        2.
% 1.99/1.01  --res_out_proof                         true
% 1.99/1.01  
% 1.99/1.01  ------ Superposition Options
% 1.99/1.01  
% 1.99/1.01  --superposition_flag                    true
% 1.99/1.01  --sup_passive_queue_type                priority_queues
% 1.99/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.01  --demod_completeness_check              fast
% 1.99/1.01  --demod_use_ground                      true
% 1.99/1.01  --sup_to_prop_solver                    passive
% 1.99/1.01  --sup_prop_simpl_new                    true
% 1.99/1.01  --sup_prop_simpl_given                  true
% 1.99/1.01  --sup_fun_splitting                     false
% 1.99/1.01  --sup_smt_interval                      50000
% 1.99/1.01  
% 1.99/1.01  ------ Superposition Simplification Setup
% 1.99/1.01  
% 1.99/1.01  --sup_indices_passive                   []
% 1.99/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.01  --sup_full_bw                           [BwDemod]
% 1.99/1.01  --sup_immed_triv                        [TrivRules]
% 1.99/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.01  --sup_immed_bw_main                     []
% 1.99/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.01  
% 1.99/1.01  ------ Combination Options
% 1.99/1.01  
% 1.99/1.01  --comb_res_mult                         3
% 1.99/1.01  --comb_sup_mult                         2
% 1.99/1.01  --comb_inst_mult                        10
% 1.99/1.01  
% 1.99/1.01  ------ Debug Options
% 1.99/1.01  
% 1.99/1.01  --dbg_backtrace                         false
% 1.99/1.01  --dbg_dump_prop_clauses                 false
% 1.99/1.01  --dbg_dump_prop_clauses_file            -
% 1.99/1.01  --dbg_out_stat                          false
% 1.99/1.01  
% 1.99/1.01  
% 1.99/1.01  
% 1.99/1.01  
% 1.99/1.01  ------ Proving...
% 1.99/1.01  
% 1.99/1.01  
% 1.99/1.01  % SZS status Theorem for theBenchmark.p
% 1.99/1.01  
% 1.99/1.01   Resolution empty clause
% 1.99/1.01  
% 1.99/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/1.01  
% 1.99/1.01  fof(f14,conjecture,(
% 1.99/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f15,negated_conjecture,(
% 1.99/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 1.99/1.01    inference(negated_conjecture,[],[f14])).
% 1.99/1.01  
% 1.99/1.01  fof(f37,plain,(
% 1.99/1.01    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.99/1.01    inference(ennf_transformation,[],[f15])).
% 1.99/1.01  
% 1.99/1.01  fof(f38,plain,(
% 1.99/1.01    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.99/1.01    inference(flattening,[],[f37])).
% 1.99/1.01  
% 1.99/1.01  fof(f40,plain,(
% 1.99/1.01    ? [X0] : (? [X1] : (? [X2] : (((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.99/1.01    inference(nnf_transformation,[],[f38])).
% 1.99/1.01  
% 1.99/1.01  fof(f41,plain,(
% 1.99/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.99/1.01    inference(flattening,[],[f40])).
% 1.99/1.01  
% 1.99/1.01  fof(f44,plain,(
% 1.99/1.01    ( ! [X0,X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r2_waybel_7(X0,X1,sK2) | ~r2_hidden(sK2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,sK2) | r2_hidden(sK2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.99/1.01    introduced(choice_axiom,[])).
% 1.99/1.01  
% 1.99/1.01  fof(f43,plain,(
% 1.99/1.01    ( ! [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r2_waybel_7(X0,sK1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)))) & (r2_waybel_7(X0,sK1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK1))) )),
% 1.99/1.01    introduced(choice_axiom,[])).
% 1.99/1.01  
% 1.99/1.01  fof(f42,plain,(
% 1.99/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_waybel_7(sK0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & (r2_waybel_7(sK0,X1,X2) | r2_hidden(X2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1)))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.99/1.01    introduced(choice_axiom,[])).
% 1.99/1.01  
% 1.99/1.01  fof(f45,plain,(
% 1.99/1.01    (((~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & (r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.99/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43,f42])).
% 1.99/1.01  
% 1.99/1.01  fof(f68,plain,(
% 1.99/1.01    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.99/1.01    inference(cnf_transformation,[],[f45])).
% 1.99/1.01  
% 1.99/1.01  fof(f8,axiom,(
% 1.99/1.01    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f53,plain,(
% 1.99/1.01    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.99/1.01    inference(cnf_transformation,[],[f8])).
% 1.99/1.01  
% 1.99/1.01  fof(f83,plain,(
% 1.99/1.01    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.99/1.01    inference(definition_unfolding,[],[f68,f53])).
% 1.99/1.01  
% 1.99/1.01  fof(f69,plain,(
% 1.99/1.01    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.99/1.01    inference(cnf_transformation,[],[f45])).
% 1.99/1.01  
% 1.99/1.01  fof(f82,plain,(
% 1.99/1.01    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.99/1.01    inference(definition_unfolding,[],[f69,f53])).
% 1.99/1.01  
% 1.99/1.01  fof(f11,axiom,(
% 1.99/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f17,plain,(
% 1.99/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/1.01    inference(pure_predicate_removal,[],[f11])).
% 1.99/1.01  
% 1.99/1.01  fof(f31,plain,(
% 1.99/1.01    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.99/1.01    inference(ennf_transformation,[],[f17])).
% 1.99/1.01  
% 1.99/1.01  fof(f32,plain,(
% 1.99/1.01    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.99/1.01    inference(flattening,[],[f31])).
% 1.99/1.01  
% 1.99/1.01  fof(f59,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f32])).
% 1.99/1.01  
% 1.99/1.01  fof(f78,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(definition_unfolding,[],[f59,f53,f53,f53,f53])).
% 1.99/1.01  
% 1.99/1.01  fof(f67,plain,(
% 1.99/1.01    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.99/1.01    inference(cnf_transformation,[],[f45])).
% 1.99/1.01  
% 1.99/1.01  fof(f84,plain,(
% 1.99/1.01    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.99/1.01    inference(definition_unfolding,[],[f67,f53])).
% 1.99/1.01  
% 1.99/1.01  fof(f66,plain,(
% 1.99/1.01    ~v1_xboole_0(sK1)),
% 1.99/1.01    inference(cnf_transformation,[],[f45])).
% 1.99/1.01  
% 1.99/1.01  fof(f5,axiom,(
% 1.99/1.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f22,plain,(
% 1.99/1.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.99/1.01    inference(ennf_transformation,[],[f5])).
% 1.99/1.01  
% 1.99/1.01  fof(f50,plain,(
% 1.99/1.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f22])).
% 1.99/1.01  
% 1.99/1.01  fof(f65,plain,(
% 1.99/1.01    l1_pre_topc(sK0)),
% 1.99/1.01    inference(cnf_transformation,[],[f45])).
% 1.99/1.01  
% 1.99/1.01  fof(f63,plain,(
% 1.99/1.01    ~v2_struct_0(sK0)),
% 1.99/1.01    inference(cnf_transformation,[],[f45])).
% 1.99/1.01  
% 1.99/1.01  fof(f10,axiom,(
% 1.99/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f16,plain,(
% 1.99/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/1.01    inference(pure_predicate_removal,[],[f10])).
% 1.99/1.01  
% 1.99/1.01  fof(f19,plain,(
% 1.99/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/1.01    inference(pure_predicate_removal,[],[f16])).
% 1.99/1.01  
% 1.99/1.01  fof(f29,plain,(
% 1.99/1.01    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.99/1.01    inference(ennf_transformation,[],[f19])).
% 1.99/1.01  
% 1.99/1.01  fof(f30,plain,(
% 1.99/1.01    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.99/1.01    inference(flattening,[],[f29])).
% 1.99/1.01  
% 1.99/1.01  fof(f57,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f30])).
% 1.99/1.01  
% 1.99/1.01  fof(f76,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(definition_unfolding,[],[f57,f53,f53,f53])).
% 1.99/1.01  
% 1.99/1.01  fof(f58,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f32])).
% 1.99/1.01  
% 1.99/1.01  fof(f79,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(definition_unfolding,[],[f58,f53,f53,f53,f53])).
% 1.99/1.01  
% 1.99/1.01  fof(f56,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f30])).
% 1.99/1.01  
% 1.99/1.01  fof(f77,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(definition_unfolding,[],[f56,f53,f53,f53])).
% 1.99/1.01  
% 1.99/1.01  fof(f73,plain,(
% 1.99/1.01    ~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 1.99/1.01    inference(cnf_transformation,[],[f45])).
% 1.99/1.01  
% 1.99/1.01  fof(f12,axiom,(
% 1.99/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f33,plain,(
% 1.99/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.99/1.01    inference(ennf_transformation,[],[f12])).
% 1.99/1.01  
% 1.99/1.01  fof(f34,plain,(
% 1.99/1.01    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/1.01    inference(flattening,[],[f33])).
% 1.99/1.01  
% 1.99/1.01  fof(f39,plain,(
% 1.99/1.01    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/1.01    inference(nnf_transformation,[],[f34])).
% 1.99/1.01  
% 1.99/1.01  fof(f60,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f39])).
% 1.99/1.01  
% 1.99/1.01  fof(f64,plain,(
% 1.99/1.01    v2_pre_topc(sK0)),
% 1.99/1.01    inference(cnf_transformation,[],[f45])).
% 1.99/1.01  
% 1.99/1.01  fof(f71,plain,(
% 1.99/1.01    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.99/1.01    inference(cnf_transformation,[],[f45])).
% 1.99/1.01  
% 1.99/1.01  fof(f9,axiom,(
% 1.99/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f18,plain,(
% 1.99/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.99/1.01    inference(pure_predicate_removal,[],[f9])).
% 1.99/1.01  
% 1.99/1.01  fof(f27,plain,(
% 1.99/1.01    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.99/1.01    inference(ennf_transformation,[],[f18])).
% 1.99/1.01  
% 1.99/1.01  fof(f28,plain,(
% 1.99/1.01    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.99/1.01    inference(flattening,[],[f27])).
% 1.99/1.01  
% 1.99/1.01  fof(f55,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f28])).
% 1.99/1.01  
% 1.99/1.01  fof(f74,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(definition_unfolding,[],[f55,f53,f53,f53])).
% 1.99/1.01  
% 1.99/1.01  fof(f4,axiom,(
% 1.99/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f21,plain,(
% 1.99/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.99/1.01    inference(ennf_transformation,[],[f4])).
% 1.99/1.01  
% 1.99/1.01  fof(f49,plain,(
% 1.99/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f21])).
% 1.99/1.01  
% 1.99/1.01  fof(f13,axiom,(
% 1.99/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f35,plain,(
% 1.99/1.01    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.99/1.01    inference(ennf_transformation,[],[f13])).
% 1.99/1.01  
% 1.99/1.01  fof(f36,plain,(
% 1.99/1.01    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.99/1.01    inference(flattening,[],[f35])).
% 1.99/1.01  
% 1.99/1.01  fof(f62,plain,(
% 1.99/1.01    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f36])).
% 1.99/1.01  
% 1.99/1.01  fof(f80,plain,(
% 1.99/1.01    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(definition_unfolding,[],[f62,f53,f53,f53,f53])).
% 1.99/1.01  
% 1.99/1.01  fof(f70,plain,(
% 1.99/1.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.99/1.01    inference(cnf_transformation,[],[f45])).
% 1.99/1.01  
% 1.99/1.01  fof(f81,plain,(
% 1.99/1.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.99/1.01    inference(definition_unfolding,[],[f70,f53])).
% 1.99/1.01  
% 1.99/1.01  fof(f72,plain,(
% 1.99/1.01    r2_waybel_7(sK0,sK1,sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 1.99/1.01    inference(cnf_transformation,[],[f45])).
% 1.99/1.01  
% 1.99/1.01  fof(f61,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f39])).
% 1.99/1.01  
% 1.99/1.01  fof(f7,axiom,(
% 1.99/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f25,plain,(
% 1.99/1.01    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.99/1.01    inference(ennf_transformation,[],[f7])).
% 1.99/1.01  
% 1.99/1.01  fof(f26,plain,(
% 1.99/1.01    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/1.01    inference(flattening,[],[f25])).
% 1.99/1.01  
% 1.99/1.01  fof(f52,plain,(
% 1.99/1.01    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f26])).
% 1.99/1.01  
% 1.99/1.01  fof(f6,axiom,(
% 1.99/1.01    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f23,plain,(
% 1.99/1.01    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.99/1.01    inference(ennf_transformation,[],[f6])).
% 1.99/1.01  
% 1.99/1.01  fof(f24,plain,(
% 1.99/1.01    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.99/1.01    inference(flattening,[],[f23])).
% 1.99/1.01  
% 1.99/1.01  fof(f51,plain,(
% 1.99/1.01    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f24])).
% 1.99/1.01  
% 1.99/1.01  fof(f3,axiom,(
% 1.99/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f20,plain,(
% 1.99/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.99/1.01    inference(ennf_transformation,[],[f3])).
% 1.99/1.01  
% 1.99/1.01  fof(f48,plain,(
% 1.99/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.99/1.01    inference(cnf_transformation,[],[f20])).
% 1.99/1.01  
% 1.99/1.01  fof(f2,axiom,(
% 1.99/1.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f47,plain,(
% 1.99/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.99/1.01    inference(cnf_transformation,[],[f2])).
% 1.99/1.01  
% 1.99/1.01  fof(f1,axiom,(
% 1.99/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 1.99/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.01  
% 1.99/1.01  fof(f46,plain,(
% 1.99/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.99/1.01    inference(cnf_transformation,[],[f1])).
% 1.99/1.01  
% 1.99/1.01  cnf(c_21,negated_conjecture,
% 1.99/1.01      ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.99/1.01      inference(cnf_transformation,[],[f83]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_20,negated_conjecture,
% 1.99/1.01      ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.99/1.01      inference(cnf_transformation,[],[f82]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_11,plain,
% 1.99/1.01      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.99/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | v1_xboole_0(X1) ),
% 1.99/1.01      inference(cnf_transformation,[],[f78]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_22,negated_conjecture,
% 1.99/1.01      ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
% 1.99/1.01      inference(cnf_transformation,[],[f84]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_355,plain,
% 1.99/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | sK1 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_356,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | v1_xboole_0(sK1)
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_355]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_23,negated_conjecture,
% 1.99/1.01      ( ~ v1_xboole_0(sK1) ),
% 1.99/1.01      inference(cnf_transformation,[],[f66]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_360,plain,
% 1.99/1.01      ( v1_xboole_0(X0)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.99/1.01      inference(global_propositional_subsumption,[status(thm)],[c_356,c_23]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_361,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_360]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1363,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | sK1 != sK1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_361]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1756,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | sK1 != sK1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_1363]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_4,plain,
% 1.99/1.01      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.99/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_24,negated_conjecture,
% 1.99/1.01      ( l1_pre_topc(sK0) ),
% 1.99/1.01      inference(cnf_transformation,[],[f65]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_569,plain,
% 1.99/1.01      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_570,plain,
% 1.99/1.01      ( l1_struct_0(sK0) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_569]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2122,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | sK1 != sK1
% 1.99/1.01      | sK0 != X1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_1756,c_570]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2123,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v2_struct_0(sK0)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_2122]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_26,negated_conjecture,
% 1.99/1.01      ( ~ v2_struct_0(sK0) ),
% 1.99/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2127,plain,
% 1.99/1.01      ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.99/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2123,c_26]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2128,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_2127]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_9,plain,
% 1.99/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | v1_xboole_0(X1) ),
% 1.99/1.01      inference(cnf_transformation,[],[f76]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1284,plain,
% 1.99/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.99/1.01      | sK1 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1285,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | v1_xboole_0(sK1)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_1284]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1289,plain,
% 1.99/1.01      ( v1_xboole_0(X0)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1285,c_23]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1290,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_1289]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1817,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | sK1 != sK1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_1290]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2095,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v4_orders_2(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | sK1 != sK1
% 1.99/1.01      | sK0 != X1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_1817,c_570]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2096,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v2_struct_0(sK0)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_2095]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2100,plain,
% 1.99/1.01      ( v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2096,c_26]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2101,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_2100]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_12,plain,
% 1.99/1.01      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.99/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | v1_xboole_0(X1) ),
% 1.99/1.01      inference(cnf_transformation,[],[f79]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_10,plain,
% 1.99/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | v1_xboole_0(X1) ),
% 1.99/1.01      inference(cnf_transformation,[],[f77]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_149,plain,
% 1.99/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | v1_xboole_0(X1) ),
% 1.99/1.01      inference(global_propositional_subsumption,[status(thm)],[c_12,c_10]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_150,plain,
% 1.99/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X1)
% 1.99/1.01      | v1_xboole_0(X0) ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_149]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1248,plain,
% 1.99/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.99/1.01      | sK1 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_150,c_20]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1249,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | v1_xboole_0(sK1)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_1248]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1253,plain,
% 1.99/1.01      ( v1_xboole_0(X0)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1249,c_23]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1254,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_1253]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1846,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | sK1 != sK1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_1254]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2068,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(X1,X0,sK1))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | sK1 != sK1
% 1.99/1.01      | sK0 != X1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_1846,c_570]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2069,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v2_struct_0(sK0)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_2068]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2073,plain,
% 1.99/1.01      ( ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2069,c_26]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2074,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_2073]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_16,negated_conjecture,
% 1.99/1.01      ( ~ r2_waybel_7(sK0,sK1,sK2)
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.99/1.01      inference(cnf_transformation,[],[f73]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_193,plain,
% 1.99/1.01      ( ~ r2_waybel_7(sK0,sK1,sK2)
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.99/1.01      inference(prop_impl,[status(thm)],[c_16]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_14,plain,
% 1.99/1.01      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.99/1.01      | ~ l1_waybel_0(X1,X0)
% 1.99/1.01      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.99/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/1.01      | ~ v7_waybel_0(X1)
% 1.99/1.01      | ~ v4_orders_2(X1)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ v2_pre_topc(X0)
% 1.99/1.01      | ~ l1_pre_topc(X0) ),
% 1.99/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_25,negated_conjecture,
% 1.99/1.01      ( v2_pre_topc(sK0) ),
% 1.99/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_445,plain,
% 1.99/1.01      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.99/1.01      | ~ l1_waybel_0(X1,X0)
% 1.99/1.01      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.99/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/1.01      | ~ v7_waybel_0(X1)
% 1.99/1.01      | ~ v4_orders_2(X1)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_pre_topc(X0)
% 1.99/1.01      | sK0 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_446,plain,
% 1.99/1.01      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.99/1.01      | ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.99/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | v2_struct_0(sK0)
% 1.99/1.01      | ~ l1_pre_topc(sK0) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_445]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_450,plain,
% 1.99/1.01      ( r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.99/1.01      | ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.99/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0) ),
% 1.99/1.01      inference(global_propositional_subsumption,
% 1.99/1.01                [status(thm)],
% 1.99/1.01                [c_446,c_26,c_24]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_905,plain,
% 1.99/1.01      ( ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,X0) != sK1
% 1.99/1.01      | sK2 != X1
% 1.99/1.01      | sK0 != sK0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_193,c_450]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_906,plain,
% 1.99/1.01      ( ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,X0) != sK1 ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_905]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_18,negated_conjecture,
% 1.99/1.01      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 1.99/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_910,plain,
% 1.99/1.01      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
% 1.99/1.01      | ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,X0) != sK1 ),
% 1.99/1.01      inference(global_propositional_subsumption,[status(thm)],[c_906,c_18]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_911,plain,
% 1.99/1.01      ( ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,X0) != sK1 ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_910]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_7,plain,
% 1.99/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | v1_xboole_0(X1) ),
% 1.99/1.01      inference(cnf_transformation,[],[f74]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1327,plain,
% 1.99/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.99/1.01      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.99/1.01      | sK1 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1328,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | v1_xboole_0(sK1)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_1327]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1332,plain,
% 1.99/1.01      ( v1_xboole_0(X0)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
% 1.99/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1328,c_23]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1333,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | l1_waybel_0(k3_yellow19(X1,X0,sK1),X1)
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_1332]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1788,plain,
% 1.99/1.01      ( l1_waybel_0(k3_yellow19(X0,X1,sK1),X0)
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | ~ l1_struct_0(X0)
% 1.99/1.01      | v1_xboole_0(X1)
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.99/1.01      | sK1 != sK1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_1333]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1946,plain,
% 1.99/1.01      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X1)
% 1.99/1.01      | k3_yellow19(X2,X1,sK1) != X0
% 1.99/1.01      | k2_yellow19(sK0,X0) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.99/1.01      | sK1 != sK1
% 1.99/1.01      | sK0 != X2 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_911,c_1788]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1947,plain,
% 1.99/1.01      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v2_struct_0(sK0)
% 1.99/1.01      | ~ l1_struct_0(sK0)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_1946]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_70,plain,
% 1.99/1.01      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.99/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1951,plain,
% 1.99/1.01      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(global_propositional_subsumption,
% 1.99/1.01                [status(thm)],
% 1.99/1.01                [c_1947,c_26,c_24,c_70]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2158,plain,
% 1.99/1.01      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_2074,c_1951]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2173,plain,
% 1.99/1.01      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_2101,c_2158]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2190,plain,
% 1.99/1.01      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
% 1.99/1.01      | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.99/1.01      inference(resolution,[status(thm)],[c_2128,c_2173]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2829,plain,
% 1.99/1.01      ( k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))) != iProver_top
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
% 1.99/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.99/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.99/1.01      | v1_xboole_0(X0) = iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_2190]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3,plain,
% 1.99/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.99/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2063,plain,
% 1.99/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_570]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2064,plain,
% 1.99/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_2063]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2886,plain,
% 1.99/1.01      ( k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))) != iProver_top
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
% 1.99/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.99/1.01      | v1_xboole_0(X0) = iProver_top ),
% 1.99/1.01      inference(light_normalisation,[status(thm)],[c_2829,c_2064]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3065,plain,
% 1.99/1.01      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
% 1.99/1.01      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/1.01      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 1.99/1.01      inference(equality_resolution,[status(thm)],[c_2886]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_15,plain,
% 1.99/1.01      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.99/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.99/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 1.99/1.01      inference(cnf_transformation,[],[f80]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_394,plain,
% 1.99/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.99/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_struct_0(X1)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/1.01      | sK1 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_395,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.99/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | ~ l1_struct_0(X0)
% 1.99/1.01      | v1_xboole_0(sK1)
% 1.99/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_394]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_399,plain,
% 1.99/1.01      ( ~ l1_struct_0(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.99/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.99/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.99/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.99/1.01      inference(global_propositional_subsumption,[status(thm)],[c_395,c_23]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_400,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.99/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | ~ l1_struct_0(X0)
% 1.99/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_399]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1398,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | ~ l1_struct_0(X0)
% 1.99/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/1.01      | sK1 != sK1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_400]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1875,plain,
% 1.99/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | ~ l1_struct_0(X0)
% 1.99/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/1.01      | sK1 != sK1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_1398]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2052,plain,
% 1.99/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/1.01      | sK1 != sK1
% 1.99/1.01      | sK0 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_1875,c_570]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2053,plain,
% 1.99/1.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.99/1.01      | v2_struct_0(sK0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_2052]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_19,negated_conjecture,
% 1.99/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
% 1.99/1.01      inference(cnf_transformation,[],[f81]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_402,plain,
% 1.99/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.99/1.01      | v2_struct_0(sK0)
% 1.99/1.01      | ~ l1_struct_0(sK0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.99/1.01      inference(instantiation,[status(thm)],[c_400]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2055,plain,
% 1.99/1.01      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.99/1.01      inference(global_propositional_subsumption,
% 1.99/1.01                [status(thm)],
% 1.99/1.01                [c_2053,c_26,c_24,c_21,c_20,c_19,c_70,c_402]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2425,plain,
% 1.99/1.01      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.99/1.01      inference(equality_resolution_simp,[status(thm)],[c_2055]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3066,plain,
% 1.99/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/1.01      | sK1 != sK1
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
% 1.99/1.01      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/1.01      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 1.99/1.01      inference(light_normalisation,[status(thm)],[c_3065,c_2425]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3067,plain,
% 1.99/1.01      ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) != iProver_top
% 1.99/1.01      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/1.01      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 1.99/1.01      inference(equality_resolution_simp,[status(thm)],[c_3066]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_34,plain,
% 1.99/1.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_17,negated_conjecture,
% 1.99/1.01      ( r2_waybel_7(sK0,sK1,sK2)
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.99/1.01      inference(cnf_transformation,[],[f72]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_195,plain,
% 1.99/1.01      ( r2_waybel_7(sK0,sK1,sK2)
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
% 1.99/1.01      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_13,plain,
% 1.99/1.01      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.99/1.01      | ~ l1_waybel_0(X1,X0)
% 1.99/1.01      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.99/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/1.01      | ~ v7_waybel_0(X1)
% 1.99/1.01      | ~ v4_orders_2(X1)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ v2_pre_topc(X0)
% 1.99/1.01      | ~ l1_pre_topc(X0) ),
% 1.99/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_478,plain,
% 1.99/1.01      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.99/1.01      | ~ l1_waybel_0(X1,X0)
% 1.99/1.01      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.99/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.99/1.01      | ~ v7_waybel_0(X1)
% 1.99/1.01      | ~ v4_orders_2(X1)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_pre_topc(X0)
% 1.99/1.01      | sK0 != X0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_479,plain,
% 1.99/1.01      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.99/1.01      | ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.99/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | v2_struct_0(sK0)
% 1.99/1.01      | ~ l1_pre_topc(sK0) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_478]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_483,plain,
% 1.99/1.01      ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.99/1.01      | ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.99/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0) ),
% 1.99/1.01      inference(global_propositional_subsumption,
% 1.99/1.01                [status(thm)],
% 1.99/1.01                [c_479,c_26,c_24]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_872,plain,
% 1.99/1.01      ( ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | r2_hidden(X1,k10_yellow_6(sK0,X0))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,X0) != sK1
% 1.99/1.01      | sK2 != X1
% 1.99/1.01      | sK0 != sK0 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_195,c_483]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_873,plain,
% 1.99/1.01      ( ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,X0))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,X0) != sK1 ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_872]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_877,plain,
% 1.99/1.01      ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,X0))
% 1.99/1.01      | ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,X0) != sK1 ),
% 1.99/1.01      inference(global_propositional_subsumption,[status(thm)],[c_873,c_18]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_878,plain,
% 1.99/1.01      ( ~ l1_waybel_0(X0,sK0)
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,X0))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,X0) != sK1 ),
% 1.99/1.01      inference(renaming,[status(thm)],[c_877]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1988,plain,
% 1.99/1.01      ( r2_hidden(sK2,k10_yellow_6(sK0,X0))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.99/1.01      | ~ v7_waybel_0(X0)
% 1.99/1.01      | ~ v4_orders_2(X0)
% 1.99/1.01      | v2_struct_0(X0)
% 1.99/1.01      | v2_struct_0(X2)
% 1.99/1.01      | ~ l1_struct_0(X2)
% 1.99/1.01      | v1_xboole_0(X1)
% 1.99/1.01      | k3_yellow19(X2,X1,sK1) != X0
% 1.99/1.01      | k2_yellow19(sK0,X0) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.99/1.01      | sK1 != sK1
% 1.99/1.01      | sK0 != X2 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_878,c_1788]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1989,plain,
% 1.99/1.01      ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v2_struct_0(sK0)
% 1.99/1.01      | ~ l1_struct_0(sK0)
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_1988]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1993,plain,
% 1.99/1.01      ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(global_propositional_subsumption,
% 1.99/1.01                [status(thm)],
% 1.99/1.01                [c_1989,c_26,c_24,c_70]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2159,plain,
% 1.99/1.01      ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | ~ v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_2074,c_1993]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2172,plain,
% 1.99/1.01      ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.99/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_2101,c_2159]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2219,plain,
% 1.99/1.01      ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
% 1.99/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.99/1.01      | v1_xboole_0(X0)
% 1.99/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.99/1.01      inference(resolution,[status(thm)],[c_2128,c_2172]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2828,plain,
% 1.99/1.01      ( k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))) = iProver_top
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
% 1.99/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.99/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.99/1.01      | v1_xboole_0(X0) = iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_2219]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2869,plain,
% 1.99/1.01      ( k2_yellow19(sK0,k3_yellow19(sK0,X0,sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.99/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,X0,sK1))) = iProver_top
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
% 1.99/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.99/1.01      | v1_xboole_0(X0) = iProver_top ),
% 1.99/1.01      inference(light_normalisation,[status(thm)],[c_2828,c_2064]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3319,plain,
% 1.99/1.01      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != sK1
% 1.99/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
% 1.99/1.01      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/1.01      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 1.99/1.01      inference(equality_resolution,[status(thm)],[c_2869]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3320,plain,
% 1.99/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.99/1.01      | sK1 != sK1
% 1.99/1.01      | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
% 1.99/1.01      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/1.01      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 1.99/1.01      inference(light_normalisation,[status(thm)],[c_3319,c_2425]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3321,plain,
% 1.99/1.01      ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) = iProver_top
% 1.99/1.01      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.99/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.99/1.01      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 1.99/1.01      inference(equality_resolution_simp,[status(thm)],[c_3320]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2834,plain,
% 1.99/1.01      ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2843,plain,
% 1.99/1.01      ( m1_subset_1(sK2,k2_struct_0(sK0)) = iProver_top ),
% 1.99/1.01      inference(light_normalisation,[status(thm)],[c_2834,c_2064]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_6,plain,
% 1.99/1.01      ( r2_hidden(X0,k1_connsp_2(X1,X0))
% 1.99/1.01      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ v2_pre_topc(X1)
% 1.99/1.01      | ~ l1_pre_topc(X1) ),
% 1.99/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_511,plain,
% 1.99/1.01      ( r2_hidden(X0,k1_connsp_2(X1,X0))
% 1.99/1.01      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_pre_topc(X1)
% 1.99/1.01      | sK0 != X1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_512,plain,
% 1.99/1.01      ( r2_hidden(X0,k1_connsp_2(sK0,X0))
% 1.99/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.99/1.01      | v2_struct_0(sK0)
% 1.99/1.01      | ~ l1_pre_topc(sK0) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_511]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_516,plain,
% 1.99/1.01      ( r2_hidden(X0,k1_connsp_2(sK0,X0))
% 1.99/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 1.99/1.01      inference(global_propositional_subsumption,
% 1.99/1.01                [status(thm)],
% 1.99/1.01                [c_512,c_26,c_24]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2831,plain,
% 1.99/1.01      ( r2_hidden(X0,k1_connsp_2(sK0,X0)) = iProver_top
% 1.99/1.01      | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2853,plain,
% 1.99/1.01      ( r2_hidden(X0,k1_connsp_2(sK0,X0)) = iProver_top
% 1.99/1.01      | m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top ),
% 1.99/1.01      inference(light_normalisation,[status(thm)],[c_2831,c_2064]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_5,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.99/1.01      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ v2_pre_topc(X1)
% 1.99/1.01      | ~ l1_pre_topc(X1) ),
% 1.99/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_529,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.99/1.01      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.99/1.01      | v2_struct_0(X1)
% 1.99/1.01      | ~ l1_pre_topc(X1)
% 1.99/1.01      | sK0 != X1 ),
% 1.99/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_530,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.99/1.01      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.99/1.01      | v2_struct_0(sK0)
% 1.99/1.01      | ~ l1_pre_topc(sK0) ),
% 1.99/1.01      inference(unflattening,[status(thm)],[c_529]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_534,plain,
% 1.99/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.99/1.01      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.99/1.01      inference(global_propositional_subsumption,
% 1.99/1.01                [status(thm)],
% 1.99/1.01                [c_530,c_26,c_24]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2830,plain,
% 1.99/1.01      ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 1.99/1.01      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2858,plain,
% 1.99/1.01      ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
% 1.99/1.01      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 1.99/1.01      inference(light_normalisation,[status(thm)],[c_2830,c_2064]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2,plain,
% 1.99/1.01      ( ~ r2_hidden(X0,X1)
% 1.99/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.99/1.01      | ~ v1_xboole_0(X2) ),
% 1.99/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2835,plain,
% 1.99/1.01      ( r2_hidden(X0,X1) != iProver_top
% 1.99/1.01      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 1.99/1.01      | v1_xboole_0(X2) != iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3158,plain,
% 1.99/1.01      ( r2_hidden(X0,k1_connsp_2(sK0,X1)) != iProver_top
% 1.99/1.01      | m1_subset_1(X1,k2_struct_0(sK0)) != iProver_top
% 1.99/1.01      | v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
% 1.99/1.01      inference(superposition,[status(thm)],[c_2858,c_2835]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3473,plain,
% 1.99/1.01      ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
% 1.99/1.01      | v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
% 1.99/1.01      inference(superposition,[status(thm)],[c_2853,c_3158]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3480,plain,
% 1.99/1.01      ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
% 1.99/1.01      inference(superposition,[status(thm)],[c_2843,c_3473]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3536,plain,
% 1.99/1.01      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.99/1.01      inference(global_propositional_subsumption,
% 1.99/1.01                [status(thm)],
% 1.99/1.01                [c_3067,c_34,c_3321,c_3480]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_1,plain,
% 1.99/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.99/1.01      inference(cnf_transformation,[],[f47]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2836,plain,
% 1.99/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.99/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_0,plain,
% 1.99/1.01      ( k2_subset_1(X0) = X0 ),
% 1.99/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_2846,plain,
% 1.99/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.99/1.01      inference(light_normalisation,[status(thm)],[c_2836,c_0]) ).
% 1.99/1.01  
% 1.99/1.01  cnf(c_3541,plain,
% 1.99/1.01      ( $false ),
% 1.99/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3536,c_2846]) ).
% 1.99/1.01  
% 1.99/1.01  
% 1.99/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/1.01  
% 1.99/1.01  ------                               Statistics
% 1.99/1.01  
% 1.99/1.01  ------ General
% 1.99/1.01  
% 1.99/1.01  abstr_ref_over_cycles:                  0
% 1.99/1.01  abstr_ref_under_cycles:                 0
% 1.99/1.01  gc_basic_clause_elim:                   0
% 1.99/1.01  forced_gc_time:                         0
% 1.99/1.01  parsing_time:                           0.008
% 1.99/1.01  unif_index_cands_time:                  0.
% 1.99/1.01  unif_index_add_time:                    0.
% 1.99/1.01  orderings_time:                         0.
% 1.99/1.01  out_proof_time:                         0.027
% 1.99/1.01  total_time:                             0.124
% 1.99/1.01  num_of_symbols:                         58
% 1.99/1.01  num_of_terms:                           2115
% 1.99/1.01  
% 1.99/1.01  ------ Preprocessing
% 1.99/1.01  
% 1.99/1.01  num_of_splits:                          0
% 1.99/1.01  num_of_split_atoms:                     0
% 1.99/1.01  num_of_reused_defs:                     0
% 1.99/1.01  num_eq_ax_congr_red:                    10
% 1.99/1.01  num_of_sem_filtered_clauses:            1
% 1.99/1.01  num_of_subtypes:                        0
% 1.99/1.01  monotx_restored_types:                  0
% 1.99/1.01  sat_num_of_epr_types:                   0
% 1.99/1.01  sat_num_of_non_cyclic_types:            0
% 1.99/1.01  sat_guarded_non_collapsed_types:        0
% 1.99/1.01  num_pure_diseq_elim:                    0
% 1.99/1.01  simp_replaced_by:                       0
% 1.99/1.01  res_preprocessed:                       91
% 1.99/1.01  prep_upred:                             0
% 1.99/1.01  prep_unflattend:                        54
% 1.99/1.01  smt_new_axioms:                         0
% 1.99/1.01  pred_elim_cands:                        3
% 1.99/1.01  pred_elim:                              11
% 1.99/1.01  pred_elim_cl:                           14
% 1.99/1.01  pred_elim_cycles:                       22
% 1.99/1.01  merged_defs:                            2
% 1.99/1.01  merged_defs_ncl:                        0
% 1.99/1.01  bin_hyper_res:                          2
% 1.99/1.01  prep_cycles:                            4
% 1.99/1.01  pred_elim_time:                         0.044
% 1.99/1.01  splitting_time:                         0.
% 1.99/1.01  sem_filter_time:                        0.
% 1.99/1.01  monotx_time:                            0.
% 1.99/1.01  subtype_inf_time:                       0.
% 1.99/1.01  
% 1.99/1.01  ------ Problem properties
% 1.99/1.01  
% 1.99/1.01  clauses:                                12
% 1.99/1.01  conjectures:                            3
% 1.99/1.01  epr:                                    1
% 1.99/1.01  horn:                                   11
% 1.99/1.01  ground:                                 5
% 1.99/1.01  unary:                                  7
% 1.99/1.01  binary:                                 2
% 1.99/1.01  lits:                                   30
% 1.99/1.01  lits_eq:                                9
% 1.99/1.01  fd_pure:                                0
% 1.99/1.01  fd_pseudo:                              0
% 1.99/1.01  fd_cond:                                0
% 1.99/1.01  fd_pseudo_cond:                         0
% 1.99/1.01  ac_symbols:                             0
% 1.99/1.01  
% 1.99/1.01  ------ Propositional Solver
% 1.99/1.01  
% 1.99/1.01  prop_solver_calls:                      26
% 1.99/1.01  prop_fast_solver_calls:                 1403
% 1.99/1.01  smt_solver_calls:                       0
% 1.99/1.01  smt_fast_solver_calls:                  0
% 1.99/1.01  prop_num_of_clauses:                    760
% 1.99/1.01  prop_preprocess_simplified:             2758
% 1.99/1.01  prop_fo_subsumed:                       50
% 1.99/1.01  prop_solver_time:                       0.
% 1.99/1.01  smt_solver_time:                        0.
% 1.99/1.01  smt_fast_solver_time:                   0.
% 1.99/1.01  prop_fast_solver_time:                  0.
% 1.99/1.01  prop_unsat_core_time:                   0.
% 1.99/1.01  
% 1.99/1.01  ------ QBF
% 1.99/1.01  
% 1.99/1.01  qbf_q_res:                              0
% 1.99/1.01  qbf_num_tautologies:                    0
% 1.99/1.01  qbf_prep_cycles:                        0
% 1.99/1.01  
% 1.99/1.01  ------ BMC1
% 1.99/1.01  
% 1.99/1.01  bmc1_current_bound:                     -1
% 1.99/1.01  bmc1_last_solved_bound:                 -1
% 1.99/1.01  bmc1_unsat_core_size:                   -1
% 1.99/1.01  bmc1_unsat_core_parents_size:           -1
% 1.99/1.01  bmc1_merge_next_fun:                    0
% 1.99/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.99/1.01  
% 1.99/1.01  ------ Instantiation
% 1.99/1.01  
% 1.99/1.01  inst_num_of_clauses:                    141
% 1.99/1.01  inst_num_in_passive:                    20
% 1.99/1.01  inst_num_in_active:                     95
% 1.99/1.01  inst_num_in_unprocessed:                26
% 1.99/1.01  inst_num_of_loops:                      100
% 1.99/1.01  inst_num_of_learning_restarts:          0
% 1.99/1.01  inst_num_moves_active_passive:          2
% 1.99/1.01  inst_lit_activity:                      0
% 1.99/1.01  inst_lit_activity_moves:                0
% 1.99/1.01  inst_num_tautologies:                   0
% 1.99/1.01  inst_num_prop_implied:                  0
% 1.99/1.01  inst_num_existing_simplified:           0
% 1.99/1.01  inst_num_eq_res_simplified:             0
% 1.99/1.01  inst_num_child_elim:                    0
% 1.99/1.01  inst_num_of_dismatching_blockings:      32
% 1.99/1.01  inst_num_of_non_proper_insts:           109
% 1.99/1.01  inst_num_of_duplicates:                 0
% 1.99/1.01  inst_inst_num_from_inst_to_res:         0
% 1.99/1.01  inst_dismatching_checking_time:         0.
% 1.99/1.01  
% 1.99/1.01  ------ Resolution
% 1.99/1.01  
% 1.99/1.01  res_num_of_clauses:                     0
% 1.99/1.01  res_num_in_passive:                     0
% 1.99/1.01  res_num_in_active:                      0
% 1.99/1.01  res_num_of_loops:                       95
% 1.99/1.01  res_forward_subset_subsumed:            10
% 1.99/1.01  res_backward_subset_subsumed:           0
% 1.99/1.01  res_forward_subsumed:                   1
% 1.99/1.01  res_backward_subsumed:                  0
% 1.99/1.01  res_forward_subsumption_resolution:     2
% 1.99/1.01  res_backward_subsumption_resolution:    4
% 1.99/1.01  res_clause_to_clause_subsumption:       137
% 1.99/1.01  res_orphan_elimination:                 0
% 1.99/1.01  res_tautology_del:                      23
% 1.99/1.01  res_num_eq_res_simplified:              1
% 1.99/1.01  res_num_sel_changes:                    0
% 1.99/1.01  res_moves_from_active_to_pass:          0
% 1.99/1.01  
% 1.99/1.01  ------ Superposition
% 1.99/1.01  
% 1.99/1.01  sup_time_total:                         0.
% 1.99/1.01  sup_time_generating:                    0.
% 1.99/1.01  sup_time_sim_full:                      0.
% 1.99/1.01  sup_time_sim_immed:                     0.
% 1.99/1.01  
% 1.99/1.01  sup_num_of_clauses:                     20
% 1.99/1.01  sup_num_in_active:                      19
% 1.99/1.01  sup_num_in_passive:                     1
% 1.99/1.01  sup_num_of_loops:                       19
% 1.99/1.01  sup_fw_superposition:                   6
% 1.99/1.01  sup_bw_superposition:                   1
% 1.99/1.01  sup_immediate_simplified:               2
% 1.99/1.01  sup_given_eliminated:                   0
% 1.99/1.01  comparisons_done:                       0
% 1.99/1.01  comparisons_avoided:                    0
% 1.99/1.01  
% 1.99/1.01  ------ Simplifications
% 1.99/1.01  
% 1.99/1.01  
% 1.99/1.01  sim_fw_subset_subsumed:                 0
% 1.99/1.01  sim_bw_subset_subsumed:                 0
% 1.99/1.01  sim_fw_subsumed:                        0
% 1.99/1.01  sim_bw_subsumed:                        0
% 1.99/1.01  sim_fw_subsumption_res:                 1
% 1.99/1.01  sim_bw_subsumption_res:                 0
% 1.99/1.01  sim_tautology_del:                      0
% 1.99/1.01  sim_eq_tautology_del:                   0
% 1.99/1.01  sim_eq_res_simp:                        2
% 1.99/1.01  sim_fw_demodulated:                     0
% 1.99/1.01  sim_bw_demodulated:                     0
% 1.99/1.01  sim_light_normalised:                   8
% 1.99/1.01  sim_joinable_taut:                      0
% 1.99/1.01  sim_joinable_simp:                      0
% 1.99/1.01  sim_ac_normalised:                      0
% 1.99/1.01  sim_smt_subsumption:                    0
% 1.99/1.01  
%------------------------------------------------------------------------------
