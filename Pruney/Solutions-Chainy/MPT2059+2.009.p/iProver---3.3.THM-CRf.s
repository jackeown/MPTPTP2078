%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:21 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  209 (1782 expanded)
%              Number of clauses        :  131 ( 394 expanded)
%              Number of leaves         :   16 ( 498 expanded)
%              Depth                    :   28
%              Number of atoms          : 1301 (14910 expanded)
%              Number of equality atoms :  215 ( 559 expanded)
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
             => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
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
               => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
                <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f34])).

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
    inference(flattening,[],[f39])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_waybel_7(X0,X1,X2)
            | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
          & ( r2_waybel_7(X0,X1,X2)
            | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r2_waybel_7(X0,X1,sK3)
          | ~ r2_hidden(sK3,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
        & ( r2_waybel_7(X0,X1,sK3)
          | r2_hidden(sK3,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
            ( ( ~ r2_waybel_7(X0,sK2,X2)
              | ~ r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK2))) )
            & ( r2_waybel_7(X0,sK2,X2)
              | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK2))) )
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
              ( ( ~ r2_waybel_7(sK1,X1,X2)
                | ~ r2_hidden(X2,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1))) )
              & ( r2_waybel_7(sK1,X1,X2)
                | r2_hidden(X2,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1))) )
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
    ( ( ~ r2_waybel_7(sK1,sK2,sK3)
      | ~ r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) )
    & ( r2_waybel_7(sK1,sK2,sK3)
      | r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) )
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

fof(f68,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(definition_unfolding,[],[f68,f50])).

fof(f65,plain,(
    ~ v1_xboole_0(sK2) ),
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

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f72,plain,
    ( ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) ),
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
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f66,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(definition_unfolding,[],[f66,f50])).

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
    ( r2_waybel_7(sK1,sK2,sK3)
    | r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

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

cnf(c_20,negated_conjecture,
    ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1105,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_1106,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK2))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1105])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1110,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1106,c_23])).

cnf(c_1111,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK2))
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1110])).

cnf(c_1566,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK2))
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1111])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_441,plain,
    ( l1_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_442,plain,
    ( l1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_1917,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k3_yellow19(X1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1566,c_442])).

cnf(c_1918,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1917])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1922,plain,
    ( ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1918,c_26])).

cnf(c_1923,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1922])).

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

cnf(c_1069,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_1070,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1069])).

cnf(c_1074,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v4_orders_2(k3_yellow19(X1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1070,c_23])).

cnf(c_1075,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1074])).

cnf(c_1595,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1075])).

cnf(c_1890,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1595,c_442])).

cnf(c_1891,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1890])).

cnf(c_1895,plain,
    ( v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1891,c_26])).

cnf(c_1896,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1895])).

cnf(c_16,negated_conjecture,
    ( ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_199,plain,
    ( ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
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

cnf(c_392,plain,
    ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_393,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r2_hidden(X1,k10_yellow_6(sK1,X0))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_397,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r2_hidden(X1,k10_yellow_6(sK1,X0))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_26,c_24])).

cnf(c_681,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_199,c_397])).

cnf(c_682,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_686,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_682,c_18])).

cnf(c_687,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(X0,sK1)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
    inference(renaming,[status(thm)],[c_686])).

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

cnf(c_1141,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_20])).

cnf(c_1142,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1141])).

cnf(c_1146,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK2),X1)
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1142,c_23])).

cnf(c_1147,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | l1_waybel_0(k3_yellow19(X1,X0,sK2),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1146])).

cnf(c_1537,plain,
    ( l1_waybel_0(k3_yellow19(X0,X1,sK2),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X0)
    | v1_xboole_0(X1)
    | ~ l1_struct_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1147])).

cnf(c_1727,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ l1_struct_0(X2)
    | k3_yellow19(X2,X1,sK2) != X0
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != sK2
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_687,c_1537])).

cnf(c_1728,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK1)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1727])).

cnf(c_73,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1732,plain,
    ( v1_xboole_0(X0)
    | ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1728,c_26,c_24,c_73])).

cnf(c_1733,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1732])).

cnf(c_1959,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1896,c_1733])).

cnf(c_1974,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1923,c_1959])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1844,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_442])).

cnf(c_1845,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_1844])).

cnf(c_70,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1847,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1845,c_26,c_24,c_70,c_73])).

cnf(c_2208,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1974,c_1847])).

cnf(c_2209,plain,
    ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2)),sK3)
    | ~ r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | ~ v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_2208])).

cnf(c_3714,plain,
    ( k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
    | r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2)),sK3) != iProver_top
    | r2_waybel_7(sK1,sK2,sK3) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2209])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1855,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_442])).

cnf(c_1856,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1855])).

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

cnf(c_1177,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | k3_lattice3(k1_lattice3(k2_struct_0(X1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_1178,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | v1_xboole_0(sK2)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_1177])).

cnf(c_1182,plain,
    ( v2_struct_0(X0)
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1178,c_23])).

cnf(c_1183,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_1182])).

cnf(c_1656,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1183])).

cnf(c_1833,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
    | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | sK2 != sK2
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1656,c_442])).

cnf(c_1834,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))
    | v2_struct_0(sK1)
    | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_1833])).

cnf(c_22,negated_conjecture,
    ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1836,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1834,c_26,c_22,c_19])).

cnf(c_2871,plain,
    ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1836])).

cnf(c_3828,plain,
    ( k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | r2_waybel_7(sK1,sK2,sK3) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3714,c_1856,c_2871])).

cnf(c_3829,plain,
    ( r2_waybel_7(sK1,sK2,sK3) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3828])).

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

cnf(c_1030,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
    | v7_waybel_0(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_20])).

cnf(c_1031,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1030])).

cnf(c_1035,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1031,c_23])).

cnf(c_1036,plain,
    ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1035])).

cnf(c_1624,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1036])).

cnf(c_1860,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK2))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | sK2 != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1624,c_442])).

cnf(c_1861,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1860])).

cnf(c_1865,plain,
    ( v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1861,c_26])).

cnf(c_1866,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1865])).

cnf(c_2002,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))
    | v7_waybel_0(k3_yellow19(sK1,X2,sK2))
    | v1_xboole_0(X2)
    | X1 = X0
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X2))
    | u1_struct_0(k3_lattice3(k1_lattice3(X2))) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_1866])).

cnf(c_2003,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2 ),
    inference(unflattening,[status(thm)],[c_2002])).

cnf(c_2189,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2
    | u1_struct_0(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2003,c_1847])).

cnf(c_2190,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))) = sK2 ),
    inference(unflattening,[status(thm)],[c_2189])).

cnf(c_3715,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))) = sK2
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2190])).

cnf(c_3756,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) = sK2
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3715,c_1856])).

cnf(c_3757,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) = sK2
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3756])).

cnf(c_3722,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3724,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ v1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1984,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | X1 = X0
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_1985,plain,
    ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(X0))
    | X0 = sK0(X0) ),
    inference(unflattening,[status(thm)],[c_1984])).

cnf(c_1989,plain,
    ( X0 = sK0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1985,c_1])).

cnf(c_3732,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3724,c_1989])).

cnf(c_1995,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != X0
    | sK0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_22])).

cnf(c_1996,plain,
    ( sK0(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != sK2 ),
    inference(unflattening,[status(thm)],[c_1995])).

cnf(c_3737,plain,
    ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != sK2 ),
    inference(demodulation,[status(thm)],[c_1996,c_1989])).

cnf(c_3762,plain,
    ( v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3757,c_3722,c_3732,c_3737])).

cnf(c_17,negated_conjecture,
    ( r2_waybel_7(sK1,sK2,sK3)
    | r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_201,plain,
    ( r2_waybel_7(sK1,sK2,sK3)
    | r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_359,plain,
    ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
    | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
    | ~ l1_waybel_0(X1,X0)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v7_waybel_0(X1)
    | ~ v4_orders_2(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_360,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_364,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_26,c_24])).

cnf(c_648,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
    | r2_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_201,c_364])).

cnf(c_649,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
    | r2_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(X0,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_653,plain,
    ( ~ l1_waybel_0(X0,sK1)
    | r2_waybel_7(sK1,sK2,sK3)
    | r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_649,c_18])).

cnf(c_654,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
    | r2_waybel_7(sK1,sK2,sK3)
    | ~ l1_waybel_0(X0,sK1)
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
    inference(renaming,[status(thm)],[c_653])).

cnf(c_1769,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
    | r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | ~ l1_struct_0(X2)
    | k3_yellow19(X2,X1,sK2) != X0
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
    | sK2 != sK2
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_654,c_1537])).

cnf(c_1770,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(sK1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(sK1)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1769])).

cnf(c_1774,plain,
    ( v1_xboole_0(X0)
    | r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1770,c_26,c_24,c_73])).

cnf(c_1775,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1774])).

cnf(c_1960,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v2_struct_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1896,c_1775])).

cnf(c_1973,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | v1_xboole_0(X0)
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1923,c_1960])).

cnf(c_2233,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
    | r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(sK1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1973,c_1847])).

cnf(c_2234,plain,
    ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2)),sK3)
    | r2_waybel_7(sK1,sK2,sK3)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
    | ~ v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
    | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_2233])).

cnf(c_3713,plain,
    ( k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
    | r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2)),sK3) = iProver_top
    | r2_waybel_7(sK1,sK2,sK3) = iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2234])).

cnf(c_3807,plain,
    ( k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
    | r2_waybel_7(sK1,sK2,sK3) = iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3713,c_1856,c_2871])).

cnf(c_3808,plain,
    ( r2_waybel_7(sK1,sK2,sK3) = iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3807])).

cnf(c_3813,plain,
    ( r2_waybel_7(sK1,sK2,sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3808,c_3762,c_3722,c_3732])).

cnf(c_3834,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3829,c_3762,c_3722,c_3732,c_3813])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.94/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.00  
% 1.94/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.94/1.00  
% 1.94/1.00  ------  iProver source info
% 1.94/1.00  
% 1.94/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.94/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.94/1.00  git: non_committed_changes: false
% 1.94/1.00  git: last_make_outside_of_git: false
% 1.94/1.00  
% 1.94/1.00  ------ 
% 1.94/1.00  
% 1.94/1.00  ------ Input Options
% 1.94/1.00  
% 1.94/1.00  --out_options                           all
% 1.94/1.00  --tptp_safe_out                         true
% 1.94/1.00  --problem_path                          ""
% 1.94/1.00  --include_path                          ""
% 1.94/1.00  --clausifier                            res/vclausify_rel
% 1.94/1.00  --clausifier_options                    --mode clausify
% 1.94/1.00  --stdin                                 false
% 1.94/1.00  --stats_out                             all
% 1.94/1.00  
% 1.94/1.00  ------ General Options
% 1.94/1.00  
% 1.94/1.00  --fof                                   false
% 1.94/1.00  --time_out_real                         305.
% 1.94/1.00  --time_out_virtual                      -1.
% 1.94/1.00  --symbol_type_check                     false
% 1.94/1.00  --clausify_out                          false
% 1.94/1.00  --sig_cnt_out                           false
% 1.94/1.00  --trig_cnt_out                          false
% 1.94/1.00  --trig_cnt_out_tolerance                1.
% 1.94/1.00  --trig_cnt_out_sk_spl                   false
% 1.94/1.00  --abstr_cl_out                          false
% 1.94/1.00  
% 1.94/1.00  ------ Global Options
% 1.94/1.00  
% 1.94/1.00  --schedule                              default
% 1.94/1.00  --add_important_lit                     false
% 1.94/1.00  --prop_solver_per_cl                    1000
% 1.94/1.00  --min_unsat_core                        false
% 1.94/1.00  --soft_assumptions                      false
% 1.94/1.00  --soft_lemma_size                       3
% 1.94/1.00  --prop_impl_unit_size                   0
% 1.94/1.00  --prop_impl_unit                        []
% 1.94/1.00  --share_sel_clauses                     true
% 1.94/1.00  --reset_solvers                         false
% 1.94/1.00  --bc_imp_inh                            [conj_cone]
% 1.94/1.00  --conj_cone_tolerance                   3.
% 1.94/1.00  --extra_neg_conj                        none
% 1.94/1.00  --large_theory_mode                     true
% 1.94/1.00  --prolific_symb_bound                   200
% 1.94/1.00  --lt_threshold                          2000
% 1.94/1.00  --clause_weak_htbl                      true
% 1.94/1.00  --gc_record_bc_elim                     false
% 1.94/1.00  
% 1.94/1.00  ------ Preprocessing Options
% 1.94/1.00  
% 1.94/1.00  --preprocessing_flag                    true
% 1.94/1.00  --time_out_prep_mult                    0.1
% 1.94/1.00  --splitting_mode                        input
% 1.94/1.00  --splitting_grd                         true
% 1.94/1.00  --splitting_cvd                         false
% 1.94/1.00  --splitting_cvd_svl                     false
% 1.94/1.00  --splitting_nvd                         32
% 1.94/1.00  --sub_typing                            true
% 1.94/1.00  --prep_gs_sim                           true
% 1.94/1.00  --prep_unflatten                        true
% 1.94/1.00  --prep_res_sim                          true
% 1.94/1.00  --prep_upred                            true
% 1.94/1.00  --prep_sem_filter                       exhaustive
% 1.94/1.00  --prep_sem_filter_out                   false
% 1.94/1.00  --pred_elim                             true
% 1.94/1.00  --res_sim_input                         true
% 1.94/1.00  --eq_ax_congr_red                       true
% 1.94/1.00  --pure_diseq_elim                       true
% 1.94/1.00  --brand_transform                       false
% 1.94/1.00  --non_eq_to_eq                          false
% 1.94/1.00  --prep_def_merge                        true
% 1.94/1.00  --prep_def_merge_prop_impl              false
% 1.94/1.00  --prep_def_merge_mbd                    true
% 1.94/1.00  --prep_def_merge_tr_red                 false
% 1.94/1.00  --prep_def_merge_tr_cl                  false
% 1.94/1.00  --smt_preprocessing                     true
% 1.94/1.00  --smt_ac_axioms                         fast
% 1.94/1.00  --preprocessed_out                      false
% 1.94/1.00  --preprocessed_stats                    false
% 1.94/1.00  
% 1.94/1.00  ------ Abstraction refinement Options
% 1.94/1.00  
% 1.94/1.00  --abstr_ref                             []
% 1.94/1.00  --abstr_ref_prep                        false
% 1.94/1.00  --abstr_ref_until_sat                   false
% 1.94/1.00  --abstr_ref_sig_restrict                funpre
% 1.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.94/1.00  --abstr_ref_under                       []
% 1.94/1.00  
% 1.94/1.00  ------ SAT Options
% 1.94/1.00  
% 1.94/1.00  --sat_mode                              false
% 1.94/1.00  --sat_fm_restart_options                ""
% 1.94/1.00  --sat_gr_def                            false
% 1.94/1.00  --sat_epr_types                         true
% 1.94/1.00  --sat_non_cyclic_types                  false
% 1.94/1.00  --sat_finite_models                     false
% 1.94/1.00  --sat_fm_lemmas                         false
% 1.94/1.00  --sat_fm_prep                           false
% 1.94/1.00  --sat_fm_uc_incr                        true
% 1.94/1.00  --sat_out_model                         small
% 1.94/1.00  --sat_out_clauses                       false
% 1.94/1.00  
% 1.94/1.00  ------ QBF Options
% 1.94/1.00  
% 1.94/1.00  --qbf_mode                              false
% 1.94/1.00  --qbf_elim_univ                         false
% 1.94/1.00  --qbf_dom_inst                          none
% 1.94/1.00  --qbf_dom_pre_inst                      false
% 1.94/1.00  --qbf_sk_in                             false
% 1.94/1.00  --qbf_pred_elim                         true
% 1.94/1.00  --qbf_split                             512
% 1.94/1.00  
% 1.94/1.00  ------ BMC1 Options
% 1.94/1.00  
% 1.94/1.00  --bmc1_incremental                      false
% 1.94/1.00  --bmc1_axioms                           reachable_all
% 1.94/1.00  --bmc1_min_bound                        0
% 1.94/1.00  --bmc1_max_bound                        -1
% 1.94/1.00  --bmc1_max_bound_default                -1
% 1.94/1.00  --bmc1_symbol_reachability              true
% 1.94/1.00  --bmc1_property_lemmas                  false
% 1.94/1.00  --bmc1_k_induction                      false
% 1.94/1.00  --bmc1_non_equiv_states                 false
% 1.94/1.00  --bmc1_deadlock                         false
% 1.94/1.00  --bmc1_ucm                              false
% 1.94/1.00  --bmc1_add_unsat_core                   none
% 1.94/1.00  --bmc1_unsat_core_children              false
% 1.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.94/1.00  --bmc1_out_stat                         full
% 1.94/1.00  --bmc1_ground_init                      false
% 1.94/1.00  --bmc1_pre_inst_next_state              false
% 1.94/1.00  --bmc1_pre_inst_state                   false
% 1.94/1.00  --bmc1_pre_inst_reach_state             false
% 1.94/1.00  --bmc1_out_unsat_core                   false
% 1.94/1.00  --bmc1_aig_witness_out                  false
% 1.94/1.00  --bmc1_verbose                          false
% 1.94/1.00  --bmc1_dump_clauses_tptp                false
% 1.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.94/1.00  --bmc1_dump_file                        -
% 1.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.94/1.00  --bmc1_ucm_extend_mode                  1
% 1.94/1.00  --bmc1_ucm_init_mode                    2
% 1.94/1.00  --bmc1_ucm_cone_mode                    none
% 1.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.94/1.00  --bmc1_ucm_relax_model                  4
% 1.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.94/1.00  --bmc1_ucm_layered_model                none
% 1.94/1.00  --bmc1_ucm_max_lemma_size               10
% 1.94/1.00  
% 1.94/1.00  ------ AIG Options
% 1.94/1.00  
% 1.94/1.00  --aig_mode                              false
% 1.94/1.00  
% 1.94/1.00  ------ Instantiation Options
% 1.94/1.00  
% 1.94/1.00  --instantiation_flag                    true
% 1.94/1.00  --inst_sos_flag                         false
% 1.94/1.00  --inst_sos_phase                        true
% 1.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.94/1.00  --inst_lit_sel_side                     num_symb
% 1.94/1.00  --inst_solver_per_active                1400
% 1.94/1.00  --inst_solver_calls_frac                1.
% 1.94/1.00  --inst_passive_queue_type               priority_queues
% 1.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.94/1.00  --inst_passive_queues_freq              [25;2]
% 1.94/1.00  --inst_dismatching                      true
% 1.94/1.00  --inst_eager_unprocessed_to_passive     true
% 1.94/1.00  --inst_prop_sim_given                   true
% 1.94/1.00  --inst_prop_sim_new                     false
% 1.94/1.00  --inst_subs_new                         false
% 1.94/1.00  --inst_eq_res_simp                      false
% 1.94/1.00  --inst_subs_given                       false
% 1.94/1.00  --inst_orphan_elimination               true
% 1.94/1.00  --inst_learning_loop_flag               true
% 1.94/1.00  --inst_learning_start                   3000
% 1.94/1.00  --inst_learning_factor                  2
% 1.94/1.00  --inst_start_prop_sim_after_learn       3
% 1.94/1.00  --inst_sel_renew                        solver
% 1.94/1.00  --inst_lit_activity_flag                true
% 1.94/1.00  --inst_restr_to_given                   false
% 1.94/1.00  --inst_activity_threshold               500
% 1.94/1.00  --inst_out_proof                        true
% 1.94/1.00  
% 1.94/1.00  ------ Resolution Options
% 1.94/1.00  
% 1.94/1.00  --resolution_flag                       true
% 1.94/1.00  --res_lit_sel                           adaptive
% 1.94/1.00  --res_lit_sel_side                      none
% 1.94/1.00  --res_ordering                          kbo
% 1.94/1.00  --res_to_prop_solver                    active
% 1.94/1.00  --res_prop_simpl_new                    false
% 1.94/1.00  --res_prop_simpl_given                  true
% 1.94/1.00  --res_passive_queue_type                priority_queues
% 1.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.94/1.00  --res_passive_queues_freq               [15;5]
% 1.94/1.00  --res_forward_subs                      full
% 1.94/1.00  --res_backward_subs                     full
% 1.94/1.00  --res_forward_subs_resolution           true
% 1.94/1.00  --res_backward_subs_resolution          true
% 1.94/1.00  --res_orphan_elimination                true
% 1.94/1.00  --res_time_limit                        2.
% 1.94/1.00  --res_out_proof                         true
% 1.94/1.00  
% 1.94/1.00  ------ Superposition Options
% 1.94/1.00  
% 1.94/1.00  --superposition_flag                    true
% 1.94/1.00  --sup_passive_queue_type                priority_queues
% 1.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.94/1.00  --demod_completeness_check              fast
% 1.94/1.00  --demod_use_ground                      true
% 1.94/1.00  --sup_to_prop_solver                    passive
% 1.94/1.00  --sup_prop_simpl_new                    true
% 1.94/1.00  --sup_prop_simpl_given                  true
% 1.94/1.00  --sup_fun_splitting                     false
% 1.94/1.00  --sup_smt_interval                      50000
% 1.94/1.00  
% 1.94/1.00  ------ Superposition Simplification Setup
% 1.94/1.00  
% 1.94/1.00  --sup_indices_passive                   []
% 1.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.00  --sup_full_bw                           [BwDemod]
% 1.94/1.00  --sup_immed_triv                        [TrivRules]
% 1.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.00  --sup_immed_bw_main                     []
% 1.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/1.00  
% 1.94/1.00  ------ Combination Options
% 1.94/1.00  
% 1.94/1.00  --comb_res_mult                         3
% 1.94/1.00  --comb_sup_mult                         2
% 1.94/1.00  --comb_inst_mult                        10
% 1.94/1.00  
% 1.94/1.00  ------ Debug Options
% 1.94/1.00  
% 1.94/1.00  --dbg_backtrace                         false
% 1.94/1.00  --dbg_dump_prop_clauses                 false
% 1.94/1.00  --dbg_dump_prop_clauses_file            -
% 1.94/1.00  --dbg_out_stat                          false
% 1.94/1.00  ------ Parsing...
% 1.94/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.94/1.00  
% 1.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 11 0s  sf_e  pe_s  pe_e 
% 1.94/1.00  
% 1.94/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.94/1.00  
% 1.94/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.94/1.00  ------ Proving...
% 1.94/1.00  ------ Problem Properties 
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  clauses                                 16
% 1.94/1.00  conjectures                             2
% 1.94/1.00  EPR                                     0
% 1.94/1.00  Horn                                    12
% 1.94/1.00  unary                                   7
% 1.94/1.00  binary                                  1
% 1.94/1.00  lits                                    57
% 1.94/1.00  lits eq                                 21
% 1.94/1.00  fd_pure                                 0
% 1.94/1.00  fd_pseudo                               0
% 1.94/1.00  fd_cond                                 0
% 1.94/1.00  fd_pseudo_cond                          0
% 1.94/1.00  AC symbols                              0
% 1.94/1.00  
% 1.94/1.00  ------ Schedule dynamic 5 is on 
% 1.94/1.00  
% 1.94/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  ------ 
% 1.94/1.00  Current options:
% 1.94/1.00  ------ 
% 1.94/1.00  
% 1.94/1.00  ------ Input Options
% 1.94/1.00  
% 1.94/1.00  --out_options                           all
% 1.94/1.00  --tptp_safe_out                         true
% 1.94/1.00  --problem_path                          ""
% 1.94/1.00  --include_path                          ""
% 1.94/1.00  --clausifier                            res/vclausify_rel
% 1.94/1.00  --clausifier_options                    --mode clausify
% 1.94/1.00  --stdin                                 false
% 1.94/1.00  --stats_out                             all
% 1.94/1.00  
% 1.94/1.00  ------ General Options
% 1.94/1.00  
% 1.94/1.00  --fof                                   false
% 1.94/1.00  --time_out_real                         305.
% 1.94/1.00  --time_out_virtual                      -1.
% 1.94/1.00  --symbol_type_check                     false
% 1.94/1.00  --clausify_out                          false
% 1.94/1.00  --sig_cnt_out                           false
% 1.94/1.00  --trig_cnt_out                          false
% 1.94/1.00  --trig_cnt_out_tolerance                1.
% 1.94/1.00  --trig_cnt_out_sk_spl                   false
% 1.94/1.00  --abstr_cl_out                          false
% 1.94/1.00  
% 1.94/1.00  ------ Global Options
% 1.94/1.00  
% 1.94/1.00  --schedule                              default
% 1.94/1.00  --add_important_lit                     false
% 1.94/1.00  --prop_solver_per_cl                    1000
% 1.94/1.00  --min_unsat_core                        false
% 1.94/1.00  --soft_assumptions                      false
% 1.94/1.00  --soft_lemma_size                       3
% 1.94/1.00  --prop_impl_unit_size                   0
% 1.94/1.00  --prop_impl_unit                        []
% 1.94/1.00  --share_sel_clauses                     true
% 1.94/1.00  --reset_solvers                         false
% 1.94/1.00  --bc_imp_inh                            [conj_cone]
% 1.94/1.00  --conj_cone_tolerance                   3.
% 1.94/1.00  --extra_neg_conj                        none
% 1.94/1.00  --large_theory_mode                     true
% 1.94/1.00  --prolific_symb_bound                   200
% 1.94/1.00  --lt_threshold                          2000
% 1.94/1.00  --clause_weak_htbl                      true
% 1.94/1.00  --gc_record_bc_elim                     false
% 1.94/1.00  
% 1.94/1.00  ------ Preprocessing Options
% 1.94/1.00  
% 1.94/1.00  --preprocessing_flag                    true
% 1.94/1.00  --time_out_prep_mult                    0.1
% 1.94/1.00  --splitting_mode                        input
% 1.94/1.00  --splitting_grd                         true
% 1.94/1.00  --splitting_cvd                         false
% 1.94/1.00  --splitting_cvd_svl                     false
% 1.94/1.00  --splitting_nvd                         32
% 1.94/1.00  --sub_typing                            true
% 1.94/1.00  --prep_gs_sim                           true
% 1.94/1.00  --prep_unflatten                        true
% 1.94/1.00  --prep_res_sim                          true
% 1.94/1.00  --prep_upred                            true
% 1.94/1.00  --prep_sem_filter                       exhaustive
% 1.94/1.00  --prep_sem_filter_out                   false
% 1.94/1.00  --pred_elim                             true
% 1.94/1.00  --res_sim_input                         true
% 1.94/1.00  --eq_ax_congr_red                       true
% 1.94/1.00  --pure_diseq_elim                       true
% 1.94/1.00  --brand_transform                       false
% 1.94/1.00  --non_eq_to_eq                          false
% 1.94/1.00  --prep_def_merge                        true
% 1.94/1.00  --prep_def_merge_prop_impl              false
% 1.94/1.00  --prep_def_merge_mbd                    true
% 1.94/1.00  --prep_def_merge_tr_red                 false
% 1.94/1.00  --prep_def_merge_tr_cl                  false
% 1.94/1.00  --smt_preprocessing                     true
% 1.94/1.00  --smt_ac_axioms                         fast
% 1.94/1.00  --preprocessed_out                      false
% 1.94/1.00  --preprocessed_stats                    false
% 1.94/1.00  
% 1.94/1.00  ------ Abstraction refinement Options
% 1.94/1.00  
% 1.94/1.00  --abstr_ref                             []
% 1.94/1.00  --abstr_ref_prep                        false
% 1.94/1.00  --abstr_ref_until_sat                   false
% 1.94/1.00  --abstr_ref_sig_restrict                funpre
% 1.94/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.94/1.00  --abstr_ref_under                       []
% 1.94/1.00  
% 1.94/1.00  ------ SAT Options
% 1.94/1.00  
% 1.94/1.00  --sat_mode                              false
% 1.94/1.00  --sat_fm_restart_options                ""
% 1.94/1.00  --sat_gr_def                            false
% 1.94/1.00  --sat_epr_types                         true
% 1.94/1.00  --sat_non_cyclic_types                  false
% 1.94/1.00  --sat_finite_models                     false
% 1.94/1.00  --sat_fm_lemmas                         false
% 1.94/1.00  --sat_fm_prep                           false
% 1.94/1.00  --sat_fm_uc_incr                        true
% 1.94/1.00  --sat_out_model                         small
% 1.94/1.00  --sat_out_clauses                       false
% 1.94/1.00  
% 1.94/1.00  ------ QBF Options
% 1.94/1.00  
% 1.94/1.00  --qbf_mode                              false
% 1.94/1.00  --qbf_elim_univ                         false
% 1.94/1.00  --qbf_dom_inst                          none
% 1.94/1.00  --qbf_dom_pre_inst                      false
% 1.94/1.00  --qbf_sk_in                             false
% 1.94/1.00  --qbf_pred_elim                         true
% 1.94/1.00  --qbf_split                             512
% 1.94/1.00  
% 1.94/1.00  ------ BMC1 Options
% 1.94/1.00  
% 1.94/1.00  --bmc1_incremental                      false
% 1.94/1.00  --bmc1_axioms                           reachable_all
% 1.94/1.00  --bmc1_min_bound                        0
% 1.94/1.00  --bmc1_max_bound                        -1
% 1.94/1.00  --bmc1_max_bound_default                -1
% 1.94/1.00  --bmc1_symbol_reachability              true
% 1.94/1.00  --bmc1_property_lemmas                  false
% 1.94/1.00  --bmc1_k_induction                      false
% 1.94/1.00  --bmc1_non_equiv_states                 false
% 1.94/1.00  --bmc1_deadlock                         false
% 1.94/1.00  --bmc1_ucm                              false
% 1.94/1.00  --bmc1_add_unsat_core                   none
% 1.94/1.00  --bmc1_unsat_core_children              false
% 1.94/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.94/1.00  --bmc1_out_stat                         full
% 1.94/1.00  --bmc1_ground_init                      false
% 1.94/1.00  --bmc1_pre_inst_next_state              false
% 1.94/1.00  --bmc1_pre_inst_state                   false
% 1.94/1.00  --bmc1_pre_inst_reach_state             false
% 1.94/1.00  --bmc1_out_unsat_core                   false
% 1.94/1.00  --bmc1_aig_witness_out                  false
% 1.94/1.00  --bmc1_verbose                          false
% 1.94/1.00  --bmc1_dump_clauses_tptp                false
% 1.94/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.94/1.00  --bmc1_dump_file                        -
% 1.94/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.94/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.94/1.00  --bmc1_ucm_extend_mode                  1
% 1.94/1.00  --bmc1_ucm_init_mode                    2
% 1.94/1.00  --bmc1_ucm_cone_mode                    none
% 1.94/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.94/1.00  --bmc1_ucm_relax_model                  4
% 1.94/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.94/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.94/1.00  --bmc1_ucm_layered_model                none
% 1.94/1.00  --bmc1_ucm_max_lemma_size               10
% 1.94/1.00  
% 1.94/1.00  ------ AIG Options
% 1.94/1.00  
% 1.94/1.00  --aig_mode                              false
% 1.94/1.00  
% 1.94/1.00  ------ Instantiation Options
% 1.94/1.00  
% 1.94/1.00  --instantiation_flag                    true
% 1.94/1.00  --inst_sos_flag                         false
% 1.94/1.00  --inst_sos_phase                        true
% 1.94/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.94/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.94/1.00  --inst_lit_sel_side                     none
% 1.94/1.00  --inst_solver_per_active                1400
% 1.94/1.00  --inst_solver_calls_frac                1.
% 1.94/1.00  --inst_passive_queue_type               priority_queues
% 1.94/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.94/1.00  --inst_passive_queues_freq              [25;2]
% 1.94/1.00  --inst_dismatching                      true
% 1.94/1.00  --inst_eager_unprocessed_to_passive     true
% 1.94/1.00  --inst_prop_sim_given                   true
% 1.94/1.00  --inst_prop_sim_new                     false
% 1.94/1.00  --inst_subs_new                         false
% 1.94/1.00  --inst_eq_res_simp                      false
% 1.94/1.00  --inst_subs_given                       false
% 1.94/1.00  --inst_orphan_elimination               true
% 1.94/1.00  --inst_learning_loop_flag               true
% 1.94/1.00  --inst_learning_start                   3000
% 1.94/1.00  --inst_learning_factor                  2
% 1.94/1.00  --inst_start_prop_sim_after_learn       3
% 1.94/1.00  --inst_sel_renew                        solver
% 1.94/1.00  --inst_lit_activity_flag                true
% 1.94/1.00  --inst_restr_to_given                   false
% 1.94/1.00  --inst_activity_threshold               500
% 1.94/1.00  --inst_out_proof                        true
% 1.94/1.00  
% 1.94/1.00  ------ Resolution Options
% 1.94/1.00  
% 1.94/1.00  --resolution_flag                       false
% 1.94/1.00  --res_lit_sel                           adaptive
% 1.94/1.00  --res_lit_sel_side                      none
% 1.94/1.00  --res_ordering                          kbo
% 1.94/1.00  --res_to_prop_solver                    active
% 1.94/1.00  --res_prop_simpl_new                    false
% 1.94/1.00  --res_prop_simpl_given                  true
% 1.94/1.00  --res_passive_queue_type                priority_queues
% 1.94/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.94/1.00  --res_passive_queues_freq               [15;5]
% 1.94/1.00  --res_forward_subs                      full
% 1.94/1.00  --res_backward_subs                     full
% 1.94/1.00  --res_forward_subs_resolution           true
% 1.94/1.00  --res_backward_subs_resolution          true
% 1.94/1.00  --res_orphan_elimination                true
% 1.94/1.00  --res_time_limit                        2.
% 1.94/1.00  --res_out_proof                         true
% 1.94/1.00  
% 1.94/1.00  ------ Superposition Options
% 1.94/1.00  
% 1.94/1.00  --superposition_flag                    true
% 1.94/1.00  --sup_passive_queue_type                priority_queues
% 1.94/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.94/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.94/1.00  --demod_completeness_check              fast
% 1.94/1.00  --demod_use_ground                      true
% 1.94/1.00  --sup_to_prop_solver                    passive
% 1.94/1.00  --sup_prop_simpl_new                    true
% 1.94/1.00  --sup_prop_simpl_given                  true
% 1.94/1.00  --sup_fun_splitting                     false
% 1.94/1.00  --sup_smt_interval                      50000
% 1.94/1.00  
% 1.94/1.00  ------ Superposition Simplification Setup
% 1.94/1.00  
% 1.94/1.00  --sup_indices_passive                   []
% 1.94/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.94/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.94/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.00  --sup_full_bw                           [BwDemod]
% 1.94/1.00  --sup_immed_triv                        [TrivRules]
% 1.94/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.94/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.00  --sup_immed_bw_main                     []
% 1.94/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.94/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.94/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.94/1.00  
% 1.94/1.00  ------ Combination Options
% 1.94/1.00  
% 1.94/1.00  --comb_res_mult                         3
% 1.94/1.00  --comb_sup_mult                         2
% 1.94/1.00  --comb_inst_mult                        10
% 1.94/1.00  
% 1.94/1.00  ------ Debug Options
% 1.94/1.00  
% 1.94/1.00  --dbg_backtrace                         false
% 1.94/1.00  --dbg_dump_prop_clauses                 false
% 1.94/1.00  --dbg_dump_prop_clauses_file            -
% 1.94/1.00  --dbg_out_stat                          false
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  ------ Proving...
% 1.94/1.00  
% 1.94/1.00  
% 1.94/1.00  % SZS status Theorem for theBenchmark.p
% 1.94/1.00  
% 1.94/1.00   Resolution empty clause
% 1.94/1.00  
% 1.94/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.94/1.00  
% 1.94/1.00  fof(f12,conjecture,(
% 1.94/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f13,negated_conjecture,(
% 1.94/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 1.94/1.00    inference(negated_conjecture,[],[f12])).
% 1.94/1.00  
% 1.94/1.00  fof(f33,plain,(
% 1.94/1.00    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.94/1.00    inference(ennf_transformation,[],[f13])).
% 1.94/1.00  
% 1.94/1.00  fof(f34,plain,(
% 1.94/1.00    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.94/1.00    inference(flattening,[],[f33])).
% 1.94/1.00  
% 1.94/1.00  fof(f39,plain,(
% 1.94/1.00    ? [X0] : (? [X1] : (? [X2] : (((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.94/1.00    inference(nnf_transformation,[],[f34])).
% 1.94/1.00  
% 1.94/1.00  fof(f40,plain,(
% 1.94/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.94/1.00    inference(flattening,[],[f39])).
% 1.94/1.00  
% 1.94/1.00  fof(f43,plain,(
% 1.94/1.00    ( ! [X0,X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r2_waybel_7(X0,X1,sK3) | ~r2_hidden(sK3,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,sK3) | r2_hidden(sK3,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.94/1.00    introduced(choice_axiom,[])).
% 1.94/1.00  
% 1.94/1.00  fof(f42,plain,(
% 1.94/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r2_waybel_7(X0,sK2,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)))) & (r2_waybel_7(X0,sK2,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK2))) )),
% 1.94/1.00    introduced(choice_axiom,[])).
% 1.94/1.00  
% 1.94/1.00  fof(f41,plain,(
% 1.94/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_waybel_7(X0,X1,X2) | ~r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_waybel_7(sK1,X1,X2) | ~r2_hidden(X2,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1)))) & (r2_waybel_7(sK1,X1,X2) | r2_hidden(X2,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),X1)))) & m1_subset_1(X2,u1_struct_0(sK1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.94/1.00    introduced(choice_axiom,[])).
% 1.94/1.00  
% 1.94/1.00  fof(f44,plain,(
% 1.94/1.00    (((~r2_waybel_7(sK1,sK2,sK3) | ~r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)))) & (r2_waybel_7(sK1,sK2,sK3) | r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)))) & m1_subset_1(sK3,u1_struct_0(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1))) & v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.94/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f43,f42,f41])).
% 1.94/1.00  
% 1.94/1.00  fof(f67,plain,(
% 1.94/1.00    v2_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 1.94/1.00    inference(cnf_transformation,[],[f44])).
% 1.94/1.00  
% 1.94/1.00  fof(f5,axiom,(
% 1.94/1.00    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f50,plain,(
% 1.94/1.00    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.94/1.00    inference(cnf_transformation,[],[f5])).
% 1.94/1.00  
% 1.94/1.00  fof(f82,plain,(
% 1.94/1.00    v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 1.94/1.00    inference(definition_unfolding,[],[f67,f50])).
% 1.94/1.00  
% 1.94/1.00  fof(f7,axiom,(
% 1.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f16,plain,(
% 1.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.94/1.00    inference(pure_predicate_removal,[],[f7])).
% 1.94/1.00  
% 1.94/1.00  fof(f23,plain,(
% 1.94/1.00    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.94/1.00    inference(ennf_transformation,[],[f16])).
% 1.94/1.00  
% 1.94/1.00  fof(f24,plain,(
% 1.94/1.00    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.94/1.00    inference(flattening,[],[f23])).
% 1.94/1.00  
% 1.94/1.00  fof(f53,plain,(
% 1.94/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(cnf_transformation,[],[f24])).
% 1.94/1.00  
% 1.94/1.00  fof(f74,plain,(
% 1.94/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(definition_unfolding,[],[f53,f50,f50,f50])).
% 1.94/1.00  
% 1.94/1.00  fof(f68,plain,(
% 1.94/1.00    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK1)))),
% 1.94/1.00    inference(cnf_transformation,[],[f44])).
% 1.94/1.00  
% 1.94/1.00  fof(f81,plain,(
% 1.94/1.00    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1))))),
% 1.94/1.00    inference(definition_unfolding,[],[f68,f50])).
% 1.94/1.00  
% 1.94/1.00  fof(f65,plain,(
% 1.94/1.00    ~v1_xboole_0(sK2)),
% 1.94/1.00    inference(cnf_transformation,[],[f44])).
% 1.94/1.00  
% 1.94/1.00  fof(f3,axiom,(
% 1.94/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f19,plain,(
% 1.94/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.94/1.00    inference(ennf_transformation,[],[f3])).
% 1.94/1.00  
% 1.94/1.00  fof(f48,plain,(
% 1.94/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.94/1.00    inference(cnf_transformation,[],[f19])).
% 1.94/1.00  
% 1.94/1.00  fof(f64,plain,(
% 1.94/1.00    l1_pre_topc(sK1)),
% 1.94/1.00    inference(cnf_transformation,[],[f44])).
% 1.94/1.00  
% 1.94/1.00  fof(f62,plain,(
% 1.94/1.00    ~v2_struct_0(sK1)),
% 1.94/1.00    inference(cnf_transformation,[],[f44])).
% 1.94/1.00  
% 1.94/1.00  fof(f8,axiom,(
% 1.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f14,plain,(
% 1.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.94/1.00    inference(pure_predicate_removal,[],[f8])).
% 1.94/1.00  
% 1.94/1.00  fof(f15,plain,(
% 1.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.94/1.00    inference(pure_predicate_removal,[],[f14])).
% 1.94/1.00  
% 1.94/1.00  fof(f25,plain,(
% 1.94/1.00    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.94/1.00    inference(ennf_transformation,[],[f15])).
% 1.94/1.00  
% 1.94/1.00  fof(f26,plain,(
% 1.94/1.00    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.94/1.00    inference(flattening,[],[f25])).
% 1.94/1.00  
% 1.94/1.00  fof(f56,plain,(
% 1.94/1.00    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(cnf_transformation,[],[f26])).
% 1.94/1.00  
% 1.94/1.00  fof(f75,plain,(
% 1.94/1.00    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(definition_unfolding,[],[f56,f50,f50,f50])).
% 1.94/1.00  
% 1.94/1.00  fof(f72,plain,(
% 1.94/1.00    ~r2_waybel_7(sK1,sK2,sK3) | ~r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)))),
% 1.94/1.00    inference(cnf_transformation,[],[f44])).
% 1.94/1.00  
% 1.94/1.00  fof(f10,axiom,(
% 1.94/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f29,plain,(
% 1.94/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.94/1.00    inference(ennf_transformation,[],[f10])).
% 1.94/1.00  
% 1.94/1.00  fof(f30,plain,(
% 1.94/1.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/1.00    inference(flattening,[],[f29])).
% 1.94/1.00  
% 1.94/1.00  fof(f38,plain,(
% 1.94/1.00    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.94/1.00    inference(nnf_transformation,[],[f30])).
% 1.94/1.00  
% 1.94/1.00  fof(f60,plain,(
% 1.94/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,k10_yellow_6(X0,X1)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(cnf_transformation,[],[f38])).
% 1.94/1.00  
% 1.94/1.00  fof(f63,plain,(
% 1.94/1.00    v2_pre_topc(sK1)),
% 1.94/1.00    inference(cnf_transformation,[],[f44])).
% 1.94/1.00  
% 1.94/1.00  fof(f70,plain,(
% 1.94/1.00    m1_subset_1(sK3,u1_struct_0(sK1))),
% 1.94/1.00    inference(cnf_transformation,[],[f44])).
% 1.94/1.00  
% 1.94/1.00  fof(f54,plain,(
% 1.94/1.00    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(cnf_transformation,[],[f24])).
% 1.94/1.00  
% 1.94/1.00  fof(f73,plain,(
% 1.94/1.00    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(definition_unfolding,[],[f54,f50,f50,f50])).
% 1.94/1.00  
% 1.94/1.00  fof(f4,axiom,(
% 1.94/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f20,plain,(
% 1.94/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.94/1.00    inference(ennf_transformation,[],[f4])).
% 1.94/1.00  
% 1.94/1.00  fof(f21,plain,(
% 1.94/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.94/1.00    inference(flattening,[],[f20])).
% 1.94/1.00  
% 1.94/1.00  fof(f49,plain,(
% 1.94/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(cnf_transformation,[],[f21])).
% 1.94/1.00  
% 1.94/1.00  fof(f2,axiom,(
% 1.94/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f18,plain,(
% 1.94/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.94/1.00    inference(ennf_transformation,[],[f2])).
% 1.94/1.00  
% 1.94/1.00  fof(f47,plain,(
% 1.94/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.94/1.00    inference(cnf_transformation,[],[f18])).
% 1.94/1.00  
% 1.94/1.00  fof(f11,axiom,(
% 1.94/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f31,plain,(
% 1.94/1.00    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.94/1.00    inference(ennf_transformation,[],[f11])).
% 1.94/1.00  
% 1.94/1.00  fof(f32,plain,(
% 1.94/1.00    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.94/1.00    inference(flattening,[],[f31])).
% 1.94/1.00  
% 1.94/1.00  fof(f61,plain,(
% 1.94/1.00    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(cnf_transformation,[],[f32])).
% 1.94/1.00  
% 1.94/1.00  fof(f79,plain,(
% 1.94/1.00    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(definition_unfolding,[],[f61,f50,f50,f50,f50])).
% 1.94/1.00  
% 1.94/1.00  fof(f66,plain,(
% 1.94/1.00    v1_subset_1(sK2,u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))),
% 1.94/1.00    inference(cnf_transformation,[],[f44])).
% 1.94/1.00  
% 1.94/1.00  fof(f83,plain,(
% 1.94/1.00    v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))),
% 1.94/1.00    inference(definition_unfolding,[],[f66,f50])).
% 1.94/1.00  
% 1.94/1.00  fof(f69,plain,(
% 1.94/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))),
% 1.94/1.00    inference(cnf_transformation,[],[f44])).
% 1.94/1.00  
% 1.94/1.00  fof(f80,plain,(
% 1.94/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))),
% 1.94/1.00    inference(definition_unfolding,[],[f69,f50])).
% 1.94/1.00  
% 1.94/1.00  fof(f6,axiom,(
% 1.94/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f22,plain,(
% 1.94/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.94/1.00    inference(ennf_transformation,[],[f6])).
% 1.94/1.00  
% 1.94/1.00  fof(f37,plain,(
% 1.94/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.94/1.00    inference(nnf_transformation,[],[f22])).
% 1.94/1.00  
% 1.94/1.00  fof(f52,plain,(
% 1.94/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.94/1.00    inference(cnf_transformation,[],[f37])).
% 1.94/1.00  
% 1.94/1.00  fof(f9,axiom,(
% 1.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f17,plain,(
% 1.94/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.94/1.00    inference(pure_predicate_removal,[],[f9])).
% 1.94/1.00  
% 1.94/1.00  fof(f27,plain,(
% 1.94/1.00    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.94/1.00    inference(ennf_transformation,[],[f17])).
% 1.94/1.00  
% 1.94/1.00  fof(f28,plain,(
% 1.94/1.00    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.94/1.00    inference(flattening,[],[f27])).
% 1.94/1.00  
% 1.94/1.00  fof(f58,plain,(
% 1.94/1.00    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(cnf_transformation,[],[f28])).
% 1.94/1.00  
% 1.94/1.00  fof(f77,plain,(
% 1.94/1.00    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(definition_unfolding,[],[f58,f50,f50,f50,f50])).
% 1.94/1.00  
% 1.94/1.00  fof(f1,axiom,(
% 1.94/1.00    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.94/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.94/1.00  
% 1.94/1.00  fof(f35,plain,(
% 1.94/1.00    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 1.94/1.00    introduced(choice_axiom,[])).
% 1.94/1.00  
% 1.94/1.00  fof(f36,plain,(
% 1.94/1.00    ! [X0] : (~v1_subset_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 1.94/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1,f35])).
% 1.94/1.00  
% 1.94/1.00  fof(f45,plain,(
% 1.94/1.00    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 1.94/1.00    inference(cnf_transformation,[],[f36])).
% 1.94/1.00  
% 1.94/1.00  fof(f46,plain,(
% 1.94/1.00    ( ! [X0] : (~v1_subset_1(sK0(X0),X0)) )),
% 1.94/1.00    inference(cnf_transformation,[],[f36])).
% 1.94/1.00  
% 1.94/1.00  fof(f71,plain,(
% 1.94/1.00    r2_waybel_7(sK1,sK2,sK3) | r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)))),
% 1.94/1.00    inference(cnf_transformation,[],[f44])).
% 1.94/1.00  
% 1.94/1.00  fof(f59,plain,(
% 1.94/1.00    ( ! [X2,X0,X1] : (r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.94/1.00    inference(cnf_transformation,[],[f38])).
% 1.94/1.00  
% 1.94/1.00  cnf(c_21,negated_conjecture,
% 1.94/1.00      ( v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.94/1.00      inference(cnf_transformation,[],[f82]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_8,plain,
% 1.94/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.94/1.00      | v2_struct_0(X2)
% 1.94/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.94/1.00      | v1_xboole_0(X1)
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | ~ l1_struct_0(X2) ),
% 1.94/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_20,negated_conjecture,
% 1.94/1.00      ( v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) ),
% 1.94/1.00      inference(cnf_transformation,[],[f81]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1105,plain,
% 1.94/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.94/1.00      | v2_struct_0(X2)
% 1.94/1.00      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.94/1.00      | v1_xboole_0(X1)
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | ~ l1_struct_0(X2)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.94/1.00      | sK2 != X0 ),
% 1.94/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1106,plain,
% 1.94/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | ~ v2_struct_0(k3_yellow19(X1,X0,sK2))
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | v1_xboole_0(sK2)
% 1.94/1.00      | ~ l1_struct_0(X1)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(unflattening,[status(thm)],[c_1105]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_23,negated_conjecture,
% 1.94/1.00      ( ~ v1_xboole_0(sK2) ),
% 1.94/1.00      inference(cnf_transformation,[],[f65]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1110,plain,
% 1.94/1.00      ( v1_xboole_0(X0)
% 1.94/1.00      | ~ v2_struct_0(k3_yellow19(X1,X0,sK2))
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.00      | ~ l1_struct_0(X1)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1106,c_23]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1111,plain,
% 1.94/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | ~ v2_struct_0(k3_yellow19(X1,X0,sK2))
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | ~ l1_struct_0(X1)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(renaming,[status(thm)],[c_1110]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1566,plain,
% 1.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | ~ v2_struct_0(k3_yellow19(X1,X0,sK2))
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | ~ l1_struct_0(X1)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.94/1.00      | sK2 != sK2 ),
% 1.94/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_1111]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_3,plain,
% 1.94/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.94/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_24,negated_conjecture,
% 1.94/1.00      ( l1_pre_topc(sK1) ),
% 1.94/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_441,plain,
% 1.94/1.00      ( l1_struct_0(X0) | sK1 != X0 ),
% 1.94/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_442,plain,
% 1.94/1.00      ( l1_struct_0(sK1) ),
% 1.94/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1917,plain,
% 1.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | ~ v2_struct_0(k3_yellow19(X1,X0,sK2))
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.94/1.00      | sK2 != sK2
% 1.94/1.00      | sK1 != X1 ),
% 1.94/1.00      inference(resolution_lifted,[status(thm)],[c_1566,c_442]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1918,plain,
% 1.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.00      | v2_struct_0(sK1)
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(unflattening,[status(thm)],[c_1917]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_26,negated_conjecture,
% 1.94/1.00      ( ~ v2_struct_0(sK1) ),
% 1.94/1.00      inference(cnf_transformation,[],[f62]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1922,plain,
% 1.94/1.00      ( ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1918,c_26]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1923,plain,
% 1.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | ~ v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(renaming,[status(thm)],[c_1922]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_9,plain,
% 1.94/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.94/1.00      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.94/1.00      | v2_struct_0(X2)
% 1.94/1.00      | v1_xboole_0(X1)
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | ~ l1_struct_0(X2) ),
% 1.94/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1069,plain,
% 1.94/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.94/1.00      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.94/1.00      | v2_struct_0(X2)
% 1.94/1.00      | v1_xboole_0(X1)
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | ~ l1_struct_0(X2)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.94/1.00      | sK2 != X0 ),
% 1.94/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1070,plain,
% 1.94/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | v4_orders_2(k3_yellow19(X1,X0,sK2))
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | v1_xboole_0(sK2)
% 1.94/1.00      | ~ l1_struct_0(X1)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(unflattening,[status(thm)],[c_1069]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1074,plain,
% 1.94/1.00      ( v1_xboole_0(X0)
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | v4_orders_2(k3_yellow19(X1,X0,sK2))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.00      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.00      | ~ l1_struct_0(X1)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1070,c_23]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1075,plain,
% 1.94/1.00      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | v4_orders_2(k3_yellow19(X1,X0,sK2))
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | ~ l1_struct_0(X1)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(renaming,[status(thm)],[c_1074]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1595,plain,
% 1.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | v4_orders_2(k3_yellow19(X1,X0,sK2))
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | ~ l1_struct_0(X1)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.94/1.00      | sK2 != sK2 ),
% 1.94/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_1075]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1890,plain,
% 1.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | v4_orders_2(k3_yellow19(X1,X0,sK2))
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.94/1.00      | sK2 != sK2
% 1.94/1.00      | sK1 != X1 ),
% 1.94/1.00      inference(resolution_lifted,[status(thm)],[c_1595,c_442]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1891,plain,
% 1.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.94/1.00      | v2_struct_0(sK1)
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(unflattening,[status(thm)],[c_1890]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1895,plain,
% 1.94/1.00      ( v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1891,c_26]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1896,plain,
% 1.94/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.00      | v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.00      inference(renaming,[status(thm)],[c_1895]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_16,negated_conjecture,
% 1.94/1.00      ( ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.00      | ~ r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) ),
% 1.94/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_199,plain,
% 1.94/1.00      ( ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.00      | ~ r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) ),
% 1.94/1.00      inference(prop_impl,[status(thm)],[c_16]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_13,plain,
% 1.94/1.00      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.94/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.94/1.00      | ~ l1_waybel_0(X1,X0)
% 1.94/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.94/1.00      | ~ v2_pre_topc(X0)
% 1.94/1.00      | ~ v7_waybel_0(X1)
% 1.94/1.00      | ~ v4_orders_2(X1)
% 1.94/1.00      | v2_struct_0(X0)
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | ~ l1_pre_topc(X0) ),
% 1.94/1.00      inference(cnf_transformation,[],[f60]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_25,negated_conjecture,
% 1.94/1.00      ( v2_pre_topc(sK1) ),
% 1.94/1.00      inference(cnf_transformation,[],[f63]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_392,plain,
% 1.94/1.00      ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.94/1.00      | r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.94/1.00      | ~ l1_waybel_0(X1,X0)
% 1.94/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.94/1.00      | ~ v7_waybel_0(X1)
% 1.94/1.00      | ~ v4_orders_2(X1)
% 1.94/1.00      | v2_struct_0(X0)
% 1.94/1.00      | v2_struct_0(X1)
% 1.94/1.00      | ~ l1_pre_topc(X0)
% 1.94/1.00      | sK1 != X0 ),
% 1.94/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_393,plain,
% 1.94/1.00      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.94/1.00      | r2_hidden(X1,k10_yellow_6(sK1,X0))
% 1.94/1.00      | ~ l1_waybel_0(X0,sK1)
% 1.94/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.94/1.00      | ~ v7_waybel_0(X0)
% 1.94/1.00      | ~ v4_orders_2(X0)
% 1.94/1.00      | v2_struct_0(X0)
% 1.94/1.00      | v2_struct_0(sK1)
% 1.94/1.00      | ~ l1_pre_topc(sK1) ),
% 1.94/1.00      inference(unflattening,[status(thm)],[c_392]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_397,plain,
% 1.94/1.00      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.94/1.00      | r2_hidden(X1,k10_yellow_6(sK1,X0))
% 1.94/1.00      | ~ l1_waybel_0(X0,sK1)
% 1.94/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.94/1.00      | ~ v7_waybel_0(X0)
% 1.94/1.00      | ~ v4_orders_2(X0)
% 1.94/1.00      | v2_struct_0(X0) ),
% 1.94/1.00      inference(global_propositional_subsumption,
% 1.94/1.00                [status(thm)],
% 1.94/1.00                [c_393,c_26,c_24]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_681,plain,
% 1.94/1.00      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.94/1.00      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.00      | ~ l1_waybel_0(X0,sK1)
% 1.94/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.94/1.00      | ~ v7_waybel_0(X0)
% 1.94/1.00      | ~ v4_orders_2(X0)
% 1.94/1.00      | v2_struct_0(X0)
% 1.94/1.00      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0)
% 1.94/1.00      | sK3 != X1 ),
% 1.94/1.00      inference(resolution_lifted,[status(thm)],[c_199,c_397]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_682,plain,
% 1.94/1.00      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
% 1.94/1.00      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.00      | ~ l1_waybel_0(X0,sK1)
% 1.94/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 1.94/1.00      | ~ v7_waybel_0(X0)
% 1.94/1.00      | ~ v4_orders_2(X0)
% 1.94/1.00      | v2_struct_0(X0)
% 1.94/1.00      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
% 1.94/1.00      inference(unflattening,[status(thm)],[c_681]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_18,negated_conjecture,
% 1.94/1.00      ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
% 1.94/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_686,plain,
% 1.94/1.00      ( ~ l1_waybel_0(X0,sK1)
% 1.94/1.00      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.00      | ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
% 1.94/1.00      | ~ v7_waybel_0(X0)
% 1.94/1.00      | ~ v4_orders_2(X0)
% 1.94/1.00      | v2_struct_0(X0)
% 1.94/1.00      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
% 1.94/1.00      inference(global_propositional_subsumption,[status(thm)],[c_682,c_18]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_687,plain,
% 1.94/1.00      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
% 1.94/1.00      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.00      | ~ l1_waybel_0(X0,sK1)
% 1.94/1.00      | ~ v7_waybel_0(X0)
% 1.94/1.00      | ~ v4_orders_2(X0)
% 1.94/1.00      | v2_struct_0(X0)
% 1.94/1.00      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
% 1.94/1.00      inference(renaming,[status(thm)],[c_686]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_7,plain,
% 1.94/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.00      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.94/1.00      | v2_struct_0(X2)
% 1.94/1.00      | v1_xboole_0(X1)
% 1.94/1.00      | v1_xboole_0(X0)
% 1.94/1.00      | ~ l1_struct_0(X2) ),
% 1.94/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.94/1.00  
% 1.94/1.00  cnf(c_1141,plain,
% 1.94/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.00      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.94/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.94/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.94/1.00      | v2_struct_0(X2)
% 1.94/1.01      | v1_xboole_0(X1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | ~ l1_struct_0(X2)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.94/1.01      | sK2 != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_20]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1142,plain,
% 1.94/1.01      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.01      | l1_waybel_0(k3_yellow19(X1,X0,sK2),X1)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | v1_xboole_0(sK2)
% 1.94/1.01      | ~ l1_struct_0(X1)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_1141]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1146,plain,
% 1.94/1.01      ( v1_xboole_0(X0)
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | l1_waybel_0(k3_yellow19(X1,X0,sK2),X1)
% 1.94/1.01      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.01      | ~ l1_struct_0(X1)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1142,c_23]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1147,plain,
% 1.94/1.01      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.01      | l1_waybel_0(k3_yellow19(X1,X0,sK2),X1)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | ~ l1_struct_0(X1)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(renaming,[status(thm)],[c_1146]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1537,plain,
% 1.94/1.01      ( l1_waybel_0(k3_yellow19(X0,X1,sK2),X0)
% 1.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | v1_xboole_0(X1)
% 1.94/1.01      | ~ l1_struct_0(X0)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.94/1.01      | sK2 != sK2 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_1147]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1727,plain,
% 1.94/1.01      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
% 1.94/1.01      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.94/1.01      | ~ v7_waybel_0(X0)
% 1.94/1.01      | ~ v4_orders_2(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | v2_struct_0(X2)
% 1.94/1.01      | v1_xboole_0(X1)
% 1.94/1.01      | ~ l1_struct_0(X2)
% 1.94/1.01      | k3_yellow19(X2,X1,sK2) != X0
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.94/1.01      | sK2 != sK2
% 1.94/1.01      | sK1 != X2 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_687,c_1537]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1728,plain,
% 1.94/1.01      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | ~ l1_struct_0(sK1)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_1727]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_73,plain,
% 1.94/1.01      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1732,plain,
% 1.94/1.01      ( v1_xboole_0(X0)
% 1.94/1.01      | ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(global_propositional_subsumption,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_1728,c_26,c_24,c_73]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1733,plain,
% 1.94/1.01      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(renaming,[status(thm)],[c_1732]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1959,plain,
% 1.94/1.01      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_1896,c_1733]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1974,plain,
% 1.94/1.01      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_1923,c_1959]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_4,plain,
% 1.94/1.01      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 1.94/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1844,plain,
% 1.94/1.01      ( v2_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_442]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1845,plain,
% 1.94/1.01      ( v2_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_1844]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_70,plain,
% 1.94/1.01      ( v2_struct_0(sK1)
% 1.94/1.01      | ~ v1_xboole_0(u1_struct_0(sK1))
% 1.94/1.01      | ~ l1_struct_0(sK1) ),
% 1.94/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1847,plain,
% 1.94/1.01      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 1.94/1.01      inference(global_propositional_subsumption,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_1845,c_26,c_24,c_70,c_73]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2208,plain,
% 1.94/1.01      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.94/1.01      | u1_struct_0(sK1) != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_1974,c_1847]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2209,plain,
% 1.94/1.01      ( ~ r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2)),sK3)
% 1.94/1.01      | ~ r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_2208]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3714,plain,
% 1.94/1.01      ( k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
% 1.94/1.01      | r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2)),sK3) != iProver_top
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3) != iProver_top
% 1.94/1.01      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2)) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_2209]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2,plain,
% 1.94/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.94/1.01      inference(cnf_transformation,[],[f47]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1855,plain,
% 1.94/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_442]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1856,plain,
% 1.94/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_1855]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_15,plain,
% 1.94/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.94/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.94/1.01      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | ~ l1_struct_0(X1)
% 1.94/1.01      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 1.94/1.01      inference(cnf_transformation,[],[f79]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1177,plain,
% 1.94/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.94/1.01      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | ~ l1_struct_0(X1)
% 1.94/1.01      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(X1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 1.94/1.01      | sK2 != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1178,plain,
% 1.94/1.01      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | v1_xboole_0(sK2)
% 1.94/1.01      | ~ l1_struct_0(X0)
% 1.94/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_1177]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1182,plain,
% 1.94/1.01      ( v2_struct_0(X0)
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.94/1.01      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.94/1.01      | ~ l1_struct_0(X0)
% 1.94/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.94/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1178,c_23]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1183,plain,
% 1.94/1.01      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | ~ l1_struct_0(X0)
% 1.94/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.94/1.01      inference(renaming,[status(thm)],[c_1182]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1656,plain,
% 1.94/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | ~ l1_struct_0(X0)
% 1.94/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 1.94/1.01      | sK2 != sK2 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_1183]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1833,plain,
% 1.94/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK2)) = sK2
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(X0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 1.94/1.01      | sK2 != sK2
% 1.94/1.01      | sK1 != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_1656,c_442]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1834,plain,
% 1.94/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_1833]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_22,negated_conjecture,
% 1.94/1.01      ( v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) ),
% 1.94/1.01      inference(cnf_transformation,[],[f83]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_19,negated_conjecture,
% 1.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) ),
% 1.94/1.01      inference(cnf_transformation,[],[f80]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1836,plain,
% 1.94/1.01      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1))) ),
% 1.94/1.01      inference(global_propositional_subsumption,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_1834,c_26,c_22,c_19]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2871,plain,
% 1.94/1.01      ( k2_yellow19(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = sK2 ),
% 1.94/1.01      inference(equality_resolution_simp,[status(thm)],[c_1836]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3828,plain,
% 1.94/1.01      ( k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3) != iProver_top
% 1.94/1.01      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 1.94/1.01      inference(light_normalisation,[status(thm)],[c_3714,c_1856,c_2871]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3829,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,sK2,sK3) != iProver_top
% 1.94/1.01      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 1.94/1.01      inference(equality_resolution_simp,[status(thm)],[c_3828]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_5,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_subset_1(X0,X1) | X0 = X1 ),
% 1.94/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_11,plain,
% 1.94/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.94/1.01      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.94/1.01      | v2_struct_0(X2)
% 1.94/1.01      | v1_xboole_0(X1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | ~ l1_struct_0(X2) ),
% 1.94/1.01      inference(cnf_transformation,[],[f77]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1030,plain,
% 1.94/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.94/1.01      | ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.94/1.01      | v2_struct_0(X2)
% 1.94/1.01      | v1_xboole_0(X1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | ~ l1_struct_0(X2)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.94/1.01      | sK2 != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_20]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1031,plain,
% 1.94/1.01      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | v1_xboole_0(sK2)
% 1.94/1.01      | ~ l1_struct_0(X1)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_1030]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1035,plain,
% 1.94/1.01      ( v1_xboole_0(X0)
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.01      | ~ l1_struct_0(X1)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1031,c_23]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1036,plain,
% 1.94/1.01      ( ~ v2_waybel_0(sK2,k3_lattice3(k1_lattice3(X0)))
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | ~ l1_struct_0(X1)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(renaming,[status(thm)],[c_1035]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1624,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | ~ l1_struct_0(X1)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.94/1.01      | sK2 != sK2 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_1036]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1860,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(X1,X0,sK2))
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.94/1.01      | sK2 != sK2
% 1.94/1.01      | sK1 != X1 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_1624,c_442]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1861,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_1860]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1865,plain,
% 1.94/1.01      ( v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1861,c_26]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1866,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v1_subset_1(sK2,u1_struct_0(k3_lattice3(k1_lattice3(X0))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(renaming,[status(thm)],[c_1865]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2002,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.94/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X2)))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,X2,sK2))
% 1.94/1.01      | v1_xboole_0(X2)
% 1.94/1.01      | X1 = X0
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X2))
% 1.94/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(X2))) != X1
% 1.94/1.01      | sK2 != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_1866]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2003,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.94/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2 ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_2002]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2189,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.94/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(X0))) = sK2
% 1.94/1.01      | u1_struct_0(sK1) != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_2003,c_1847]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2190,plain,
% 1.94/1.01      ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
% 1.94/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))) = sK2 ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_2189]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3715,plain,
% 1.94/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
% 1.94/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))) = sK2
% 1.94/1.01      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2)) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_2190]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3756,plain,
% 1.94/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 1.94/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) = sK2
% 1.94/1.01      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
% 1.94/1.01      inference(light_normalisation,[status(thm)],[c_3715,c_1856]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3757,plain,
% 1.94/1.01      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) = sK2
% 1.94/1.01      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
% 1.94/1.01      inference(equality_resolution_simp,[status(thm)],[c_3756]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3722,plain,
% 1.94/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1,plain,
% 1.94/1.01      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 1.94/1.01      inference(cnf_transformation,[],[f45]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3724,plain,
% 1.94/1.01      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_0,plain,
% 1.94/1.01      ( ~ v1_subset_1(sK0(X0),X0) ),
% 1.94/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1984,plain,
% 1.94/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.94/1.01      | X1 != X2
% 1.94/1.01      | X1 = X0
% 1.94/1.01      | sK0(X2) != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1985,plain,
% 1.94/1.01      ( ~ m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) | X0 = sK0(X0) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_1984]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1989,plain,
% 1.94/1.01      ( X0 = sK0(X0) ),
% 1.94/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1985,c_1]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3732,plain,
% 1.94/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.94/1.01      inference(light_normalisation,[status(thm)],[c_3724,c_1989]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1995,plain,
% 1.94/1.01      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != X0
% 1.94/1.01      | sK0(X0) != sK2 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_22]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1996,plain,
% 1.94/1.01      ( sK0(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1))))) != sK2 ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_1995]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3737,plain,
% 1.94/1.01      ( u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))) != sK2 ),
% 1.94/1.01      inference(demodulation,[status(thm)],[c_1996,c_1989]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3762,plain,
% 1.94/1.01      ( v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) = iProver_top ),
% 1.94/1.01      inference(forward_subsumption_resolution,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_3757,c_3722,c_3732,c_3737]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_17,negated_conjecture,
% 1.94/1.01      ( r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) ),
% 1.94/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_201,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | r2_hidden(sK3,k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))) ),
% 1.94/1.01      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_14,plain,
% 1.94/1.01      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.94/1.01      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.94/1.01      | ~ l1_waybel_0(X1,X0)
% 1.94/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.94/1.01      | ~ v2_pre_topc(X0)
% 1.94/1.01      | ~ v7_waybel_0(X1)
% 1.94/1.01      | ~ v4_orders_2(X1)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | ~ l1_pre_topc(X0) ),
% 1.94/1.01      inference(cnf_transformation,[],[f59]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_359,plain,
% 1.94/1.01      ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.94/1.01      | ~ r2_hidden(X2,k10_yellow_6(X0,X1))
% 1.94/1.01      | ~ l1_waybel_0(X1,X0)
% 1.94/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.94/1.01      | ~ v7_waybel_0(X1)
% 1.94/1.01      | ~ v4_orders_2(X1)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | v2_struct_0(X1)
% 1.94/1.01      | ~ l1_pre_topc(X0)
% 1.94/1.01      | sK1 != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_360,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.94/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
% 1.94/1.01      | ~ l1_waybel_0(X0,sK1)
% 1.94/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.94/1.01      | ~ v7_waybel_0(X0)
% 1.94/1.01      | ~ v4_orders_2(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | ~ l1_pre_topc(sK1) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_359]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_364,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.94/1.01      | ~ r2_hidden(X1,k10_yellow_6(sK1,X0))
% 1.94/1.01      | ~ l1_waybel_0(X0,sK1)
% 1.94/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.94/1.01      | ~ v7_waybel_0(X0)
% 1.94/1.01      | ~ v4_orders_2(X0)
% 1.94/1.01      | v2_struct_0(X0) ),
% 1.94/1.01      inference(global_propositional_subsumption,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_360,c_26,c_24]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_648,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),X1)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ l1_waybel_0(X0,sK1)
% 1.94/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.94/1.01      | ~ v7_waybel_0(X0)
% 1.94/1.01      | ~ v4_orders_2(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0)
% 1.94/1.01      | sK3 != X1 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_201,c_364]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_649,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ l1_waybel_0(X0,sK1)
% 1.94/1.01      | ~ m1_subset_1(sK3,u1_struct_0(sK1))
% 1.94/1.01      | ~ v7_waybel_0(X0)
% 1.94/1.01      | ~ v4_orders_2(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_648]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_653,plain,
% 1.94/1.01      ( ~ l1_waybel_0(X0,sK1)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
% 1.94/1.01      | ~ v7_waybel_0(X0)
% 1.94/1.01      | ~ v4_orders_2(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
% 1.94/1.01      inference(global_propositional_subsumption,[status(thm)],[c_649,c_18]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_654,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ l1_waybel_0(X0,sK1)
% 1.94/1.01      | ~ v7_waybel_0(X0)
% 1.94/1.01      | ~ v4_orders_2(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0) ),
% 1.94/1.01      inference(renaming,[status(thm)],[c_653]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1769,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,X0),sK3)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.94/1.01      | ~ v7_waybel_0(X0)
% 1.94/1.01      | ~ v4_orders_2(X0)
% 1.94/1.01      | v2_struct_0(X0)
% 1.94/1.01      | v2_struct_0(X2)
% 1.94/1.01      | v1_xboole_0(X1)
% 1.94/1.01      | ~ l1_struct_0(X2)
% 1.94/1.01      | k3_yellow19(X2,X1,sK2) != X0
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,X0)
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X1))
% 1.94/1.01      | sK2 != sK2
% 1.94/1.01      | sK1 != X2 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_654,c_1537]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1770,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v2_struct_0(sK1)
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | ~ l1_struct_0(sK1)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_1769]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1774,plain,
% 1.94/1.01      ( v1_xboole_0(X0)
% 1.94/1.01      | r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(global_propositional_subsumption,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_1770,c_26,c_24,c_73]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1775,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | ~ v4_orders_2(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(renaming,[status(thm)],[c_1774]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1960,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v2_struct_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_1896,c_1775]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_1973,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | v1_xboole_0(X0)
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.94/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_1923,c_1960]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2233,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,X0,sK2)),sK3)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,X0,sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(X0))
% 1.94/1.01      | u1_struct_0(sK1) != X0 ),
% 1.94/1.01      inference(resolution_lifted,[status(thm)],[c_1973,c_1847]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_2234,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2)),sK3)
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3)
% 1.94/1.01      | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.94/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1))))))
% 1.94/1.01      | ~ v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2))
% 1.94/1.01      | k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1))) ),
% 1.94/1.01      inference(unflattening,[status(thm)],[c_2233]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3713,plain,
% 1.94/1.01      ( k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(u1_struct_0(sK1)))
% 1.94/1.01      | r2_waybel_7(sK1,k2_yellow19(sK1,k3_yellow19(sK1,u1_struct_0(sK1),sK2)),sK3) = iProver_top
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3) = iProver_top
% 1.94/1.01      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(u1_struct_0(sK1)))))) != iProver_top
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,u1_struct_0(sK1),sK2)) != iProver_top ),
% 1.94/1.01      inference(predicate_to_equality,[status(thm)],[c_2234]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3807,plain,
% 1.94/1.01      ( k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != k10_yellow_6(sK1,k3_yellow19(sK1,k2_struct_0(sK1),sK2))
% 1.94/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK1))) != k3_lattice3(k1_lattice3(k2_struct_0(sK1)))
% 1.94/1.01      | r2_waybel_7(sK1,sK2,sK3) = iProver_top
% 1.94/1.01      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 1.94/1.01      inference(light_normalisation,[status(thm)],[c_3713,c_1856,c_2871]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3808,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,sK2,sK3) = iProver_top
% 1.94/1.01      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.94/1.01      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK1)))))) != iProver_top
% 1.94/1.01      | v7_waybel_0(k3_yellow19(sK1,k2_struct_0(sK1),sK2)) != iProver_top ),
% 1.94/1.01      inference(equality_resolution_simp,[status(thm)],[c_3807]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3813,plain,
% 1.94/1.01      ( r2_waybel_7(sK1,sK2,sK3) = iProver_top ),
% 1.94/1.01      inference(forward_subsumption_resolution,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_3808,c_3762,c_3722,c_3732]) ).
% 1.94/1.01  
% 1.94/1.01  cnf(c_3834,plain,
% 1.94/1.01      ( $false ),
% 1.94/1.01      inference(forward_subsumption_resolution,
% 1.94/1.01                [status(thm)],
% 1.94/1.01                [c_3829,c_3762,c_3722,c_3732,c_3813]) ).
% 1.94/1.01  
% 1.94/1.01  
% 1.94/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.94/1.01  
% 1.94/1.01  ------                               Statistics
% 1.94/1.01  
% 1.94/1.01  ------ General
% 1.94/1.01  
% 1.94/1.01  abstr_ref_over_cycles:                  0
% 1.94/1.01  abstr_ref_under_cycles:                 0
% 1.94/1.01  gc_basic_clause_elim:                   0
% 1.94/1.01  forced_gc_time:                         0
% 1.94/1.01  parsing_time:                           0.013
% 1.94/1.01  unif_index_cands_time:                  0.
% 1.94/1.01  unif_index_add_time:                    0.
% 1.94/1.01  orderings_time:                         0.
% 1.94/1.01  out_proof_time:                         0.015
% 1.94/1.01  total_time:                             0.159
% 1.94/1.01  num_of_symbols:                         57
% 1.94/1.01  num_of_terms:                           1281
% 1.94/1.01  
% 1.94/1.01  ------ Preprocessing
% 1.94/1.01  
% 1.94/1.01  num_of_splits:                          0
% 1.94/1.01  num_of_split_atoms:                     0
% 1.94/1.01  num_of_reused_defs:                     0
% 1.94/1.01  num_eq_ax_congr_red:                    4
% 1.94/1.01  num_of_sem_filtered_clauses:            1
% 1.94/1.01  num_of_subtypes:                        0
% 1.94/1.01  monotx_restored_types:                  0
% 1.94/1.01  sat_num_of_epr_types:                   0
% 1.94/1.01  sat_num_of_non_cyclic_types:            0
% 1.94/1.01  sat_guarded_non_collapsed_types:        0
% 1.94/1.01  num_pure_diseq_elim:                    0
% 1.94/1.01  simp_replaced_by:                       0
% 1.94/1.01  res_preprocessed:                       102
% 1.94/1.01  prep_upred:                             0
% 1.94/1.01  prep_unflattend:                        58
% 1.94/1.01  smt_new_axioms:                         0
% 1.94/1.01  pred_elim_cands:                        3
% 1.94/1.01  pred_elim:                              11
% 1.94/1.01  pred_elim_cl:                           9
% 1.94/1.01  pred_elim_cycles:                       21
% 1.94/1.01  merged_defs:                            2
% 1.94/1.01  merged_defs_ncl:                        0
% 1.94/1.01  bin_hyper_res:                          2
% 1.94/1.01  prep_cycles:                            4
% 1.94/1.01  pred_elim_time:                         0.08
% 1.94/1.01  splitting_time:                         0.
% 1.94/1.01  sem_filter_time:                        0.
% 1.94/1.01  monotx_time:                            0.
% 1.94/1.01  subtype_inf_time:                       0.
% 1.94/1.01  
% 1.94/1.01  ------ Problem properties
% 1.94/1.01  
% 1.94/1.01  clauses:                                16
% 1.94/1.01  conjectures:                            2
% 1.94/1.01  epr:                                    0
% 1.94/1.01  horn:                                   12
% 1.94/1.01  ground:                                 14
% 1.94/1.01  unary:                                  7
% 1.94/1.01  binary:                                 1
% 1.94/1.01  lits:                                   57
% 1.94/1.01  lits_eq:                                21
% 1.94/1.01  fd_pure:                                0
% 1.94/1.01  fd_pseudo:                              0
% 1.94/1.01  fd_cond:                                0
% 1.94/1.01  fd_pseudo_cond:                         0
% 1.94/1.01  ac_symbols:                             0
% 1.94/1.01  
% 1.94/1.01  ------ Propositional Solver
% 1.94/1.01  
% 1.94/1.01  prop_solver_calls:                      21
% 1.94/1.01  prop_fast_solver_calls:                 1633
% 1.94/1.01  smt_solver_calls:                       0
% 1.94/1.01  smt_fast_solver_calls:                  0
% 1.94/1.01  prop_num_of_clauses:                    463
% 1.94/1.01  prop_preprocess_simplified:             2133
% 1.94/1.01  prop_fo_subsumed:                       36
% 1.94/1.01  prop_solver_time:                       0.
% 1.94/1.01  smt_solver_time:                        0.
% 1.94/1.01  smt_fast_solver_time:                   0.
% 1.94/1.01  prop_fast_solver_time:                  0.
% 1.94/1.01  prop_unsat_core_time:                   0.
% 1.94/1.01  
% 1.94/1.01  ------ QBF
% 1.94/1.01  
% 1.94/1.01  qbf_q_res:                              0
% 1.94/1.01  qbf_num_tautologies:                    0
% 1.94/1.01  qbf_prep_cycles:                        0
% 1.94/1.01  
% 1.94/1.01  ------ BMC1
% 1.94/1.01  
% 1.94/1.01  bmc1_current_bound:                     -1
% 1.94/1.01  bmc1_last_solved_bound:                 -1
% 1.94/1.01  bmc1_unsat_core_size:                   -1
% 1.94/1.01  bmc1_unsat_core_parents_size:           -1
% 1.94/1.01  bmc1_merge_next_fun:                    0
% 1.94/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.94/1.01  
% 1.94/1.01  ------ Instantiation
% 1.94/1.01  
% 1.94/1.01  inst_num_of_clauses:                    30
% 1.94/1.01  inst_num_in_passive:                    0
% 1.94/1.01  inst_num_in_active:                     0
% 1.94/1.01  inst_num_in_unprocessed:                30
% 1.94/1.01  inst_num_of_loops:                      0
% 1.94/1.01  inst_num_of_learning_restarts:          0
% 1.94/1.01  inst_num_moves_active_passive:          0
% 1.94/1.01  inst_lit_activity:                      0
% 1.94/1.01  inst_lit_activity_moves:                0
% 1.94/1.01  inst_num_tautologies:                   0
% 1.94/1.01  inst_num_prop_implied:                  0
% 1.94/1.01  inst_num_existing_simplified:           0
% 1.94/1.01  inst_num_eq_res_simplified:             0
% 1.94/1.01  inst_num_child_elim:                    0
% 1.94/1.01  inst_num_of_dismatching_blockings:      0
% 1.94/1.01  inst_num_of_non_proper_insts:           0
% 1.94/1.01  inst_num_of_duplicates:                 0
% 1.94/1.01  inst_inst_num_from_inst_to_res:         0
% 1.94/1.01  inst_dismatching_checking_time:         0.
% 1.94/1.01  
% 1.94/1.01  ------ Resolution
% 1.94/1.01  
% 1.94/1.01  res_num_of_clauses:                     0
% 1.94/1.01  res_num_in_passive:                     0
% 1.94/1.01  res_num_in_active:                      0
% 1.94/1.01  res_num_of_loops:                       106
% 1.94/1.01  res_forward_subset_subsumed:            0
% 1.94/1.01  res_backward_subset_subsumed:           0
% 1.94/1.01  res_forward_subsumed:                   0
% 1.94/1.01  res_backward_subsumed:                  0
% 1.94/1.01  res_forward_subsumption_resolution:     14
% 1.94/1.01  res_backward_subsumption_resolution:    4
% 1.94/1.01  res_clause_to_clause_subsumption:       315
% 1.94/1.01  res_orphan_elimination:                 0
% 1.94/1.01  res_tautology_del:                      7
% 1.94/1.01  res_num_eq_res_simplified:              1
% 1.94/1.01  res_num_sel_changes:                    0
% 1.94/1.01  res_moves_from_active_to_pass:          0
% 1.94/1.01  
% 1.94/1.01  ------ Superposition
% 1.94/1.01  
% 1.94/1.01  sup_time_total:                         0.
% 1.94/1.01  sup_time_generating:                    0.
% 1.94/1.01  sup_time_sim_full:                      0.
% 1.94/1.01  sup_time_sim_immed:                     0.
% 1.94/1.01  
% 1.94/1.01  sup_num_of_clauses:                     0
% 1.94/1.01  sup_num_in_active:                      0
% 1.94/1.01  sup_num_in_passive:                     0
% 1.94/1.01  sup_num_of_loops:                       0
% 1.94/1.01  sup_fw_superposition:                   0
% 1.94/1.01  sup_bw_superposition:                   0
% 1.94/1.01  sup_immediate_simplified:               0
% 1.94/1.01  sup_given_eliminated:                   0
% 1.94/1.01  comparisons_done:                       0
% 1.94/1.01  comparisons_avoided:                    0
% 1.94/1.01  
% 1.94/1.01  ------ Simplifications
% 1.94/1.01  
% 1.94/1.01  
% 1.94/1.01  sim_fw_subset_subsumed:                 0
% 1.94/1.01  sim_bw_subset_subsumed:                 0
% 1.94/1.01  sim_fw_subsumed:                        1
% 1.94/1.01  sim_bw_subsumed:                        1
% 1.94/1.01  sim_fw_subsumption_res:                 11
% 1.94/1.01  sim_bw_subsumption_res:                 1
% 1.94/1.01  sim_tautology_del:                      0
% 1.94/1.01  sim_eq_tautology_del:                   0
% 1.94/1.01  sim_eq_res_simp:                        4
% 1.94/1.01  sim_fw_demodulated:                     1
% 1.94/1.01  sim_bw_demodulated:                     0
% 1.94/1.01  sim_light_normalised:                   10
% 1.94/1.01  sim_joinable_taut:                      0
% 1.94/1.01  sim_joinable_simp:                      0
% 1.94/1.01  sim_ac_normalised:                      0
% 1.94/1.01  sim_smt_subsumption:                    0
% 1.94/1.01  
%------------------------------------------------------------------------------
