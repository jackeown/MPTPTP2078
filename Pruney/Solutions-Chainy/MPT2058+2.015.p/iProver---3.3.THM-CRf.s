%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:17 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  239 (2039 expanded)
%              Number of clauses        :  157 ( 465 expanded)
%              Number of leaves         :   17 ( 560 expanded)
%              Depth                    :   33
%              Number of atoms          : 1485 (18072 expanded)
%              Number of equality atoms :  250 ( 605 expanded)
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
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43,f42])).

fof(f68,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f70,f53])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f73,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
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
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f72,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

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

cnf(c_386,plain,
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

cnf(c_387,plain,
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
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_391,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_23])).

cnf(c_392,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_4,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_604,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_605,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_1420,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_392,c_605])).

cnf(c_1421,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1420])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1425,plain,
    ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1421,c_26])).

cnf(c_1426,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1425])).

cnf(c_1866,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_1426])).

cnf(c_2144,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1866])).

cnf(c_3042,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2144])).

cnf(c_4107,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3042])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1342,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_605])).

cnf(c_1343,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1342])).

cnf(c_4198,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4107,c_1343])).

cnf(c_4705,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4198])).

cnf(c_4959,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4705])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

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

cnf(c_16,negated_conjecture,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_193,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_509,plain,
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

cnf(c_510,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_514,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_510,c_26,c_24])).

cnf(c_933,plain,
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
    inference(resolution_lifted,[status(thm)],[c_193,c_514])).

cnf(c_934,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_933])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_936,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_934,c_18])).

cnf(c_937,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_936])).

cnf(c_973,plain,
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
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_937])).

cnf(c_974,plain,
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
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_973])).

cnf(c_70,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_978,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_974,c_26,c_24,c_70])).

cnf(c_1821,plain,
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
    inference(resolution_lifted,[status(thm)],[c_978,c_20])).

cnf(c_1822,plain,
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
    inference(unflattening,[status(thm)],[c_1821])).

cnf(c_1826,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1822,c_23])).

cnf(c_1827,plain,
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
    inference(renaming,[status(thm)],[c_1826])).

cnf(c_2170,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_1827])).

cnf(c_3038,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2170])).

cnf(c_3805,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3038])).

cnf(c_4108,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
    | r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3805])).

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

cnf(c_425,plain,
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

cnf(c_426,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK1)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_430,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_23])).

cnf(c_431,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(renaming,[status(thm)],[c_430])).

cnf(c_1331,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_431,c_605])).

cnf(c_1332,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_1331])).

cnf(c_1334,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1332,c_26,c_21,c_20,c_19])).

cnf(c_3046,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_1334])).

cnf(c_4211,plain,
    ( r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4108,c_3046])).

cnf(c_17,negated_conjecture,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_195,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_476,plain,
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

cnf(c_477,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_481,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_26,c_24])).

cnf(c_907,plain,
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
    inference(resolution_lifted,[status(thm)],[c_195,c_481])).

cnf(c_908,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_907])).

cnf(c_910,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,sK1,sK2)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_908,c_18])).

cnf(c_911,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_910])).

cnf(c_1021,plain,
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
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_911])).

cnf(c_1022,plain,
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
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_1021])).

cnf(c_1026,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1022,c_26,c_24,c_70])).

cnf(c_1776,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1026,c_20])).

cnf(c_1777,plain,
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
    inference(unflattening,[status(thm)],[c_1776])).

cnf(c_1781,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1777,c_23])).

cnf(c_1782,plain,
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
    inference(renaming,[status(thm)],[c_1781])).

cnf(c_2208,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_1782])).

cnf(c_3034,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2208])).

cnf(c_3806,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3034])).

cnf(c_4110,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3806])).

cnf(c_4187,plain,
    ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4110,c_3046])).

cnf(c_4217,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4211,c_4187])).

cnf(c_4119,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4129,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4119,c_1343])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_563,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_564,c_26,c_24])).

cnf(c_4114,plain,
    ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_4139,plain,
    ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4114,c_1343])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_connsp_2(X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X3)
    | X0 != X4
    | k1_connsp_2(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_542,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_356,c_25])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_26,c_24])).

cnf(c_4115,plain,
    ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_4144,plain,
    ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4115,c_1343])).

cnf(c_4370,plain,
    ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4139,c_4144])).

cnf(c_4764,plain,
    ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4129,c_4370])).

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

cnf(c_1347,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_150,c_605])).

cnf(c_1348,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1347])).

cnf(c_1352,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1348,c_26])).

cnf(c_1353,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1352])).

cnf(c_1746,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1353,c_20])).

cnf(c_1747,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1746])).

cnf(c_1751,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1747,c_23])).

cnf(c_1752,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1751])).

cnf(c_2246,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1752])).

cnf(c_3030,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2246])).

cnf(c_4112,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,X0,sK1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3030])).

cnf(c_4162,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,X0,sK1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4112,c_1343])).

cnf(c_4607,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4162])).

cnf(c_4793,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4607,c_34,c_4764])).

cnf(c_4794,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4793])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_4120,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4132,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4120,c_0])).

cnf(c_4799,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4794,c_4132])).

cnf(c_3804,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3038])).

cnf(c_4109,plain,
    ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3804])).

cnf(c_4173,plain,
    ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4109,c_1343])).

cnf(c_4696,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4173])).

cnf(c_4801,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4696])).

cnf(c_4803,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4801,c_34,c_4764])).

cnf(c_4809,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4803,c_4132])).

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

cnf(c_1380,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_605])).

cnf(c_1381,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1380])).

cnf(c_1385,plain,
    ( v4_orders_2(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1381,c_26])).

cnf(c_1386,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1385])).

cnf(c_1716,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1386,c_20])).

cnf(c_1717,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1716])).

cnf(c_1721,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1717,c_23])).

cnf(c_1722,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1721])).

cnf(c_2269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_1722])).

cnf(c_3026,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2269])).

cnf(c_4113,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,X0,sK1)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3026])).

cnf(c_4151,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,X0,sK1)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4113,c_1343])).

cnf(c_4599,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4151])).

cnf(c_4872,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4599,c_34,c_4764])).

cnf(c_4873,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4872])).

cnf(c_4878,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4873,c_4132])).

cnf(c_4961,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4959,c_34,c_4217,c_4764,c_4799,c_4809,c_4878])).

cnf(c_4966,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4961,c_4132])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:28:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 1.74/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.02  
% 1.74/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.74/1.02  
% 1.74/1.02  ------  iProver source info
% 1.74/1.02  
% 1.74/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.74/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.74/1.02  git: non_committed_changes: false
% 1.74/1.02  git: last_make_outside_of_git: false
% 1.74/1.02  
% 1.74/1.02  ------ 
% 1.74/1.02  
% 1.74/1.02  ------ Input Options
% 1.74/1.02  
% 1.74/1.02  --out_options                           all
% 1.74/1.02  --tptp_safe_out                         true
% 1.74/1.02  --problem_path                          ""
% 1.74/1.02  --include_path                          ""
% 1.74/1.02  --clausifier                            res/vclausify_rel
% 1.74/1.02  --clausifier_options                    --mode clausify
% 1.74/1.02  --stdin                                 false
% 1.74/1.02  --stats_out                             all
% 1.74/1.02  
% 1.74/1.02  ------ General Options
% 1.74/1.02  
% 1.74/1.02  --fof                                   false
% 1.74/1.02  --time_out_real                         305.
% 1.74/1.02  --time_out_virtual                      -1.
% 1.74/1.02  --symbol_type_check                     false
% 1.74/1.02  --clausify_out                          false
% 1.74/1.02  --sig_cnt_out                           false
% 1.74/1.02  --trig_cnt_out                          false
% 1.74/1.02  --trig_cnt_out_tolerance                1.
% 1.74/1.02  --trig_cnt_out_sk_spl                   false
% 1.74/1.02  --abstr_cl_out                          false
% 1.74/1.02  
% 1.74/1.02  ------ Global Options
% 1.74/1.02  
% 1.74/1.02  --schedule                              default
% 1.74/1.02  --add_important_lit                     false
% 1.74/1.02  --prop_solver_per_cl                    1000
% 1.74/1.02  --min_unsat_core                        false
% 1.74/1.02  --soft_assumptions                      false
% 1.74/1.02  --soft_lemma_size                       3
% 1.74/1.02  --prop_impl_unit_size                   0
% 1.74/1.02  --prop_impl_unit                        []
% 1.74/1.02  --share_sel_clauses                     true
% 1.74/1.02  --reset_solvers                         false
% 1.74/1.02  --bc_imp_inh                            [conj_cone]
% 1.74/1.02  --conj_cone_tolerance                   3.
% 1.74/1.02  --extra_neg_conj                        none
% 1.74/1.02  --large_theory_mode                     true
% 1.74/1.02  --prolific_symb_bound                   200
% 1.74/1.02  --lt_threshold                          2000
% 1.74/1.02  --clause_weak_htbl                      true
% 1.74/1.02  --gc_record_bc_elim                     false
% 1.74/1.02  
% 1.74/1.02  ------ Preprocessing Options
% 1.74/1.02  
% 1.74/1.02  --preprocessing_flag                    true
% 1.74/1.02  --time_out_prep_mult                    0.1
% 1.74/1.02  --splitting_mode                        input
% 1.74/1.02  --splitting_grd                         true
% 1.74/1.02  --splitting_cvd                         false
% 1.74/1.02  --splitting_cvd_svl                     false
% 1.74/1.02  --splitting_nvd                         32
% 1.74/1.02  --sub_typing                            true
% 1.74/1.02  --prep_gs_sim                           true
% 1.74/1.02  --prep_unflatten                        true
% 1.74/1.02  --prep_res_sim                          true
% 1.74/1.02  --prep_upred                            true
% 1.74/1.02  --prep_sem_filter                       exhaustive
% 1.74/1.02  --prep_sem_filter_out                   false
% 1.74/1.02  --pred_elim                             true
% 1.74/1.02  --res_sim_input                         true
% 1.74/1.02  --eq_ax_congr_red                       true
% 1.74/1.02  --pure_diseq_elim                       true
% 1.74/1.02  --brand_transform                       false
% 1.74/1.02  --non_eq_to_eq                          false
% 1.74/1.02  --prep_def_merge                        true
% 1.74/1.02  --prep_def_merge_prop_impl              false
% 1.74/1.02  --prep_def_merge_mbd                    true
% 1.74/1.02  --prep_def_merge_tr_red                 false
% 1.74/1.02  --prep_def_merge_tr_cl                  false
% 1.74/1.02  --smt_preprocessing                     true
% 1.74/1.02  --smt_ac_axioms                         fast
% 1.74/1.02  --preprocessed_out                      false
% 1.74/1.02  --preprocessed_stats                    false
% 1.74/1.02  
% 1.74/1.02  ------ Abstraction refinement Options
% 1.74/1.02  
% 1.74/1.02  --abstr_ref                             []
% 1.74/1.02  --abstr_ref_prep                        false
% 1.74/1.02  --abstr_ref_until_sat                   false
% 1.74/1.02  --abstr_ref_sig_restrict                funpre
% 1.74/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.74/1.02  --abstr_ref_under                       []
% 1.74/1.02  
% 1.74/1.02  ------ SAT Options
% 1.74/1.02  
% 1.74/1.02  --sat_mode                              false
% 1.74/1.02  --sat_fm_restart_options                ""
% 1.74/1.02  --sat_gr_def                            false
% 1.74/1.02  --sat_epr_types                         true
% 1.74/1.02  --sat_non_cyclic_types                  false
% 1.74/1.02  --sat_finite_models                     false
% 1.74/1.02  --sat_fm_lemmas                         false
% 1.74/1.02  --sat_fm_prep                           false
% 1.74/1.02  --sat_fm_uc_incr                        true
% 1.74/1.02  --sat_out_model                         small
% 1.74/1.02  --sat_out_clauses                       false
% 1.74/1.02  
% 1.74/1.02  ------ QBF Options
% 1.74/1.02  
% 1.74/1.02  --qbf_mode                              false
% 1.74/1.02  --qbf_elim_univ                         false
% 1.74/1.02  --qbf_dom_inst                          none
% 1.74/1.02  --qbf_dom_pre_inst                      false
% 1.74/1.02  --qbf_sk_in                             false
% 1.74/1.02  --qbf_pred_elim                         true
% 1.74/1.02  --qbf_split                             512
% 1.74/1.02  
% 1.74/1.02  ------ BMC1 Options
% 1.74/1.02  
% 1.74/1.02  --bmc1_incremental                      false
% 1.74/1.02  --bmc1_axioms                           reachable_all
% 1.74/1.02  --bmc1_min_bound                        0
% 1.74/1.02  --bmc1_max_bound                        -1
% 1.74/1.02  --bmc1_max_bound_default                -1
% 1.74/1.02  --bmc1_symbol_reachability              true
% 1.74/1.02  --bmc1_property_lemmas                  false
% 1.74/1.02  --bmc1_k_induction                      false
% 1.74/1.02  --bmc1_non_equiv_states                 false
% 1.74/1.02  --bmc1_deadlock                         false
% 1.74/1.02  --bmc1_ucm                              false
% 1.74/1.02  --bmc1_add_unsat_core                   none
% 1.74/1.02  --bmc1_unsat_core_children              false
% 1.74/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.74/1.02  --bmc1_out_stat                         full
% 1.74/1.02  --bmc1_ground_init                      false
% 1.74/1.02  --bmc1_pre_inst_next_state              false
% 1.74/1.02  --bmc1_pre_inst_state                   false
% 1.74/1.02  --bmc1_pre_inst_reach_state             false
% 1.74/1.02  --bmc1_out_unsat_core                   false
% 1.74/1.02  --bmc1_aig_witness_out                  false
% 1.74/1.02  --bmc1_verbose                          false
% 1.74/1.02  --bmc1_dump_clauses_tptp                false
% 1.74/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.74/1.02  --bmc1_dump_file                        -
% 1.74/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.74/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.74/1.02  --bmc1_ucm_extend_mode                  1
% 1.74/1.02  --bmc1_ucm_init_mode                    2
% 1.74/1.02  --bmc1_ucm_cone_mode                    none
% 1.74/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.74/1.02  --bmc1_ucm_relax_model                  4
% 1.74/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.74/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.74/1.02  --bmc1_ucm_layered_model                none
% 1.74/1.02  --bmc1_ucm_max_lemma_size               10
% 1.74/1.02  
% 1.74/1.02  ------ AIG Options
% 1.74/1.02  
% 1.74/1.02  --aig_mode                              false
% 1.74/1.02  
% 1.74/1.02  ------ Instantiation Options
% 1.74/1.02  
% 1.74/1.02  --instantiation_flag                    true
% 1.74/1.02  --inst_sos_flag                         false
% 1.74/1.02  --inst_sos_phase                        true
% 1.74/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.74/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.74/1.02  --inst_lit_sel_side                     num_symb
% 1.74/1.02  --inst_solver_per_active                1400
% 1.74/1.02  --inst_solver_calls_frac                1.
% 1.74/1.02  --inst_passive_queue_type               priority_queues
% 1.74/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.74/1.02  --inst_passive_queues_freq              [25;2]
% 1.74/1.02  --inst_dismatching                      true
% 1.74/1.02  --inst_eager_unprocessed_to_passive     true
% 1.74/1.02  --inst_prop_sim_given                   true
% 1.74/1.02  --inst_prop_sim_new                     false
% 1.74/1.02  --inst_subs_new                         false
% 1.74/1.02  --inst_eq_res_simp                      false
% 1.74/1.02  --inst_subs_given                       false
% 1.74/1.02  --inst_orphan_elimination               true
% 1.74/1.02  --inst_learning_loop_flag               true
% 1.74/1.02  --inst_learning_start                   3000
% 1.74/1.02  --inst_learning_factor                  2
% 1.74/1.02  --inst_start_prop_sim_after_learn       3
% 1.74/1.02  --inst_sel_renew                        solver
% 1.74/1.02  --inst_lit_activity_flag                true
% 1.74/1.02  --inst_restr_to_given                   false
% 1.74/1.02  --inst_activity_threshold               500
% 1.74/1.02  --inst_out_proof                        true
% 1.74/1.02  
% 1.74/1.02  ------ Resolution Options
% 1.74/1.02  
% 1.74/1.02  --resolution_flag                       true
% 1.74/1.02  --res_lit_sel                           adaptive
% 1.74/1.02  --res_lit_sel_side                      none
% 1.74/1.02  --res_ordering                          kbo
% 1.74/1.02  --res_to_prop_solver                    active
% 1.74/1.02  --res_prop_simpl_new                    false
% 1.74/1.02  --res_prop_simpl_given                  true
% 1.74/1.02  --res_passive_queue_type                priority_queues
% 1.74/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.74/1.02  --res_passive_queues_freq               [15;5]
% 1.74/1.02  --res_forward_subs                      full
% 1.74/1.02  --res_backward_subs                     full
% 1.74/1.02  --res_forward_subs_resolution           true
% 1.74/1.02  --res_backward_subs_resolution          true
% 1.74/1.02  --res_orphan_elimination                true
% 1.74/1.02  --res_time_limit                        2.
% 1.74/1.02  --res_out_proof                         true
% 1.74/1.02  
% 1.74/1.02  ------ Superposition Options
% 1.74/1.02  
% 1.74/1.02  --superposition_flag                    true
% 1.74/1.02  --sup_passive_queue_type                priority_queues
% 1.74/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.74/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.74/1.02  --demod_completeness_check              fast
% 1.74/1.02  --demod_use_ground                      true
% 1.74/1.02  --sup_to_prop_solver                    passive
% 1.74/1.02  --sup_prop_simpl_new                    true
% 1.74/1.02  --sup_prop_simpl_given                  true
% 1.74/1.02  --sup_fun_splitting                     false
% 1.74/1.02  --sup_smt_interval                      50000
% 1.74/1.02  
% 1.74/1.02  ------ Superposition Simplification Setup
% 1.74/1.02  
% 1.74/1.02  --sup_indices_passive                   []
% 1.74/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.74/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.02  --sup_full_bw                           [BwDemod]
% 1.74/1.02  --sup_immed_triv                        [TrivRules]
% 1.74/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.74/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.02  --sup_immed_bw_main                     []
% 1.74/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.74/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.02  
% 1.74/1.02  ------ Combination Options
% 1.74/1.02  
% 1.74/1.02  --comb_res_mult                         3
% 1.74/1.02  --comb_sup_mult                         2
% 1.74/1.02  --comb_inst_mult                        10
% 1.74/1.02  
% 1.74/1.02  ------ Debug Options
% 1.74/1.02  
% 1.74/1.02  --dbg_backtrace                         false
% 1.74/1.02  --dbg_dump_prop_clauses                 false
% 1.74/1.02  --dbg_dump_prop_clauses_file            -
% 1.74/1.02  --dbg_out_stat                          false
% 1.74/1.02  ------ Parsing...
% 1.74/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.74/1.02  
% 1.74/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.74/1.02  
% 1.74/1.02  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.74/1.02  
% 1.74/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.74/1.02  ------ Proving...
% 1.74/1.02  ------ Problem Properties 
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  clauses                                 17
% 1.74/1.02  conjectures                             4
% 1.74/1.02  EPR                                     2
% 1.74/1.02  Horn                                    13
% 1.74/1.02  unary                                   8
% 1.74/1.02  binary                                  1
% 1.74/1.02  lits                                    53
% 1.74/1.02  lits eq                                 11
% 1.74/1.02  fd_pure                                 0
% 1.74/1.02  fd_pseudo                               0
% 1.74/1.02  fd_cond                                 0
% 1.74/1.02  fd_pseudo_cond                          0
% 1.74/1.02  AC symbols                              0
% 1.74/1.02  
% 1.74/1.02  ------ Schedule dynamic 5 is on 
% 1.74/1.02  
% 1.74/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  ------ 
% 1.74/1.02  Current options:
% 1.74/1.02  ------ 
% 1.74/1.02  
% 1.74/1.02  ------ Input Options
% 1.74/1.02  
% 1.74/1.02  --out_options                           all
% 1.74/1.02  --tptp_safe_out                         true
% 1.74/1.02  --problem_path                          ""
% 1.74/1.02  --include_path                          ""
% 1.74/1.02  --clausifier                            res/vclausify_rel
% 1.74/1.02  --clausifier_options                    --mode clausify
% 1.74/1.02  --stdin                                 false
% 1.74/1.02  --stats_out                             all
% 1.74/1.02  
% 1.74/1.02  ------ General Options
% 1.74/1.02  
% 1.74/1.02  --fof                                   false
% 1.74/1.02  --time_out_real                         305.
% 1.74/1.02  --time_out_virtual                      -1.
% 1.74/1.02  --symbol_type_check                     false
% 1.74/1.02  --clausify_out                          false
% 1.74/1.02  --sig_cnt_out                           false
% 1.74/1.02  --trig_cnt_out                          false
% 1.74/1.02  --trig_cnt_out_tolerance                1.
% 1.74/1.02  --trig_cnt_out_sk_spl                   false
% 1.74/1.02  --abstr_cl_out                          false
% 1.74/1.02  
% 1.74/1.02  ------ Global Options
% 1.74/1.02  
% 1.74/1.02  --schedule                              default
% 1.74/1.02  --add_important_lit                     false
% 1.74/1.02  --prop_solver_per_cl                    1000
% 1.74/1.02  --min_unsat_core                        false
% 1.74/1.02  --soft_assumptions                      false
% 1.74/1.02  --soft_lemma_size                       3
% 1.74/1.02  --prop_impl_unit_size                   0
% 1.74/1.02  --prop_impl_unit                        []
% 1.74/1.02  --share_sel_clauses                     true
% 1.74/1.02  --reset_solvers                         false
% 1.74/1.02  --bc_imp_inh                            [conj_cone]
% 1.74/1.02  --conj_cone_tolerance                   3.
% 1.74/1.02  --extra_neg_conj                        none
% 1.74/1.02  --large_theory_mode                     true
% 1.74/1.02  --prolific_symb_bound                   200
% 1.74/1.02  --lt_threshold                          2000
% 1.74/1.02  --clause_weak_htbl                      true
% 1.74/1.02  --gc_record_bc_elim                     false
% 1.74/1.02  
% 1.74/1.02  ------ Preprocessing Options
% 1.74/1.02  
% 1.74/1.02  --preprocessing_flag                    true
% 1.74/1.02  --time_out_prep_mult                    0.1
% 1.74/1.02  --splitting_mode                        input
% 1.74/1.02  --splitting_grd                         true
% 1.74/1.02  --splitting_cvd                         false
% 1.74/1.02  --splitting_cvd_svl                     false
% 1.74/1.02  --splitting_nvd                         32
% 1.74/1.02  --sub_typing                            true
% 1.74/1.02  --prep_gs_sim                           true
% 1.74/1.02  --prep_unflatten                        true
% 1.74/1.02  --prep_res_sim                          true
% 1.74/1.02  --prep_upred                            true
% 1.74/1.02  --prep_sem_filter                       exhaustive
% 1.74/1.02  --prep_sem_filter_out                   false
% 1.74/1.02  --pred_elim                             true
% 1.74/1.02  --res_sim_input                         true
% 1.74/1.02  --eq_ax_congr_red                       true
% 1.74/1.02  --pure_diseq_elim                       true
% 1.74/1.02  --brand_transform                       false
% 1.74/1.02  --non_eq_to_eq                          false
% 1.74/1.02  --prep_def_merge                        true
% 1.74/1.02  --prep_def_merge_prop_impl              false
% 1.74/1.02  --prep_def_merge_mbd                    true
% 1.74/1.02  --prep_def_merge_tr_red                 false
% 1.74/1.02  --prep_def_merge_tr_cl                  false
% 1.74/1.02  --smt_preprocessing                     true
% 1.74/1.02  --smt_ac_axioms                         fast
% 1.74/1.02  --preprocessed_out                      false
% 1.74/1.02  --preprocessed_stats                    false
% 1.74/1.02  
% 1.74/1.02  ------ Abstraction refinement Options
% 1.74/1.02  
% 1.74/1.02  --abstr_ref                             []
% 1.74/1.02  --abstr_ref_prep                        false
% 1.74/1.02  --abstr_ref_until_sat                   false
% 1.74/1.02  --abstr_ref_sig_restrict                funpre
% 1.74/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.74/1.02  --abstr_ref_under                       []
% 1.74/1.02  
% 1.74/1.02  ------ SAT Options
% 1.74/1.02  
% 1.74/1.02  --sat_mode                              false
% 1.74/1.02  --sat_fm_restart_options                ""
% 1.74/1.02  --sat_gr_def                            false
% 1.74/1.02  --sat_epr_types                         true
% 1.74/1.02  --sat_non_cyclic_types                  false
% 1.74/1.02  --sat_finite_models                     false
% 1.74/1.02  --sat_fm_lemmas                         false
% 1.74/1.02  --sat_fm_prep                           false
% 1.74/1.02  --sat_fm_uc_incr                        true
% 1.74/1.02  --sat_out_model                         small
% 1.74/1.02  --sat_out_clauses                       false
% 1.74/1.02  
% 1.74/1.02  ------ QBF Options
% 1.74/1.02  
% 1.74/1.02  --qbf_mode                              false
% 1.74/1.02  --qbf_elim_univ                         false
% 1.74/1.02  --qbf_dom_inst                          none
% 1.74/1.02  --qbf_dom_pre_inst                      false
% 1.74/1.02  --qbf_sk_in                             false
% 1.74/1.02  --qbf_pred_elim                         true
% 1.74/1.02  --qbf_split                             512
% 1.74/1.02  
% 1.74/1.02  ------ BMC1 Options
% 1.74/1.02  
% 1.74/1.02  --bmc1_incremental                      false
% 1.74/1.02  --bmc1_axioms                           reachable_all
% 1.74/1.02  --bmc1_min_bound                        0
% 1.74/1.02  --bmc1_max_bound                        -1
% 1.74/1.02  --bmc1_max_bound_default                -1
% 1.74/1.02  --bmc1_symbol_reachability              true
% 1.74/1.02  --bmc1_property_lemmas                  false
% 1.74/1.02  --bmc1_k_induction                      false
% 1.74/1.02  --bmc1_non_equiv_states                 false
% 1.74/1.02  --bmc1_deadlock                         false
% 1.74/1.02  --bmc1_ucm                              false
% 1.74/1.02  --bmc1_add_unsat_core                   none
% 1.74/1.02  --bmc1_unsat_core_children              false
% 1.74/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.74/1.02  --bmc1_out_stat                         full
% 1.74/1.02  --bmc1_ground_init                      false
% 1.74/1.02  --bmc1_pre_inst_next_state              false
% 1.74/1.02  --bmc1_pre_inst_state                   false
% 1.74/1.02  --bmc1_pre_inst_reach_state             false
% 1.74/1.02  --bmc1_out_unsat_core                   false
% 1.74/1.02  --bmc1_aig_witness_out                  false
% 1.74/1.02  --bmc1_verbose                          false
% 1.74/1.02  --bmc1_dump_clauses_tptp                false
% 1.74/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.74/1.02  --bmc1_dump_file                        -
% 1.74/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.74/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.74/1.02  --bmc1_ucm_extend_mode                  1
% 1.74/1.02  --bmc1_ucm_init_mode                    2
% 1.74/1.02  --bmc1_ucm_cone_mode                    none
% 1.74/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.74/1.02  --bmc1_ucm_relax_model                  4
% 1.74/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.74/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.74/1.02  --bmc1_ucm_layered_model                none
% 1.74/1.02  --bmc1_ucm_max_lemma_size               10
% 1.74/1.02  
% 1.74/1.02  ------ AIG Options
% 1.74/1.02  
% 1.74/1.02  --aig_mode                              false
% 1.74/1.02  
% 1.74/1.02  ------ Instantiation Options
% 1.74/1.02  
% 1.74/1.02  --instantiation_flag                    true
% 1.74/1.02  --inst_sos_flag                         false
% 1.74/1.02  --inst_sos_phase                        true
% 1.74/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.74/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.74/1.02  --inst_lit_sel_side                     none
% 1.74/1.02  --inst_solver_per_active                1400
% 1.74/1.02  --inst_solver_calls_frac                1.
% 1.74/1.02  --inst_passive_queue_type               priority_queues
% 1.74/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.74/1.02  --inst_passive_queues_freq              [25;2]
% 1.74/1.02  --inst_dismatching                      true
% 1.74/1.02  --inst_eager_unprocessed_to_passive     true
% 1.74/1.02  --inst_prop_sim_given                   true
% 1.74/1.02  --inst_prop_sim_new                     false
% 1.74/1.02  --inst_subs_new                         false
% 1.74/1.02  --inst_eq_res_simp                      false
% 1.74/1.02  --inst_subs_given                       false
% 1.74/1.02  --inst_orphan_elimination               true
% 1.74/1.02  --inst_learning_loop_flag               true
% 1.74/1.02  --inst_learning_start                   3000
% 1.74/1.02  --inst_learning_factor                  2
% 1.74/1.02  --inst_start_prop_sim_after_learn       3
% 1.74/1.02  --inst_sel_renew                        solver
% 1.74/1.02  --inst_lit_activity_flag                true
% 1.74/1.02  --inst_restr_to_given                   false
% 1.74/1.02  --inst_activity_threshold               500
% 1.74/1.02  --inst_out_proof                        true
% 1.74/1.02  
% 1.74/1.02  ------ Resolution Options
% 1.74/1.02  
% 1.74/1.02  --resolution_flag                       false
% 1.74/1.02  --res_lit_sel                           adaptive
% 1.74/1.02  --res_lit_sel_side                      none
% 1.74/1.02  --res_ordering                          kbo
% 1.74/1.02  --res_to_prop_solver                    active
% 1.74/1.02  --res_prop_simpl_new                    false
% 1.74/1.02  --res_prop_simpl_given                  true
% 1.74/1.02  --res_passive_queue_type                priority_queues
% 1.74/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.74/1.02  --res_passive_queues_freq               [15;5]
% 1.74/1.02  --res_forward_subs                      full
% 1.74/1.02  --res_backward_subs                     full
% 1.74/1.02  --res_forward_subs_resolution           true
% 1.74/1.02  --res_backward_subs_resolution          true
% 1.74/1.02  --res_orphan_elimination                true
% 1.74/1.02  --res_time_limit                        2.
% 1.74/1.02  --res_out_proof                         true
% 1.74/1.02  
% 1.74/1.02  ------ Superposition Options
% 1.74/1.02  
% 1.74/1.02  --superposition_flag                    true
% 1.74/1.02  --sup_passive_queue_type                priority_queues
% 1.74/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.74/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.74/1.02  --demod_completeness_check              fast
% 1.74/1.02  --demod_use_ground                      true
% 1.74/1.02  --sup_to_prop_solver                    passive
% 1.74/1.02  --sup_prop_simpl_new                    true
% 1.74/1.02  --sup_prop_simpl_given                  true
% 1.74/1.02  --sup_fun_splitting                     false
% 1.74/1.02  --sup_smt_interval                      50000
% 1.74/1.02  
% 1.74/1.02  ------ Superposition Simplification Setup
% 1.74/1.02  
% 1.74/1.02  --sup_indices_passive                   []
% 1.74/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.74/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.74/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.02  --sup_full_bw                           [BwDemod]
% 1.74/1.02  --sup_immed_triv                        [TrivRules]
% 1.74/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.74/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.02  --sup_immed_bw_main                     []
% 1.74/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.74/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.74/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.74/1.02  
% 1.74/1.02  ------ Combination Options
% 1.74/1.02  
% 1.74/1.02  --comb_res_mult                         3
% 1.74/1.02  --comb_sup_mult                         2
% 1.74/1.02  --comb_inst_mult                        10
% 1.74/1.02  
% 1.74/1.02  ------ Debug Options
% 1.74/1.02  
% 1.74/1.02  --dbg_backtrace                         false
% 1.74/1.02  --dbg_dump_prop_clauses                 false
% 1.74/1.02  --dbg_dump_prop_clauses_file            -
% 1.74/1.02  --dbg_out_stat                          false
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  ------ Proving...
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  % SZS status Theorem for theBenchmark.p
% 1.74/1.02  
% 1.74/1.02   Resolution empty clause
% 1.74/1.02  
% 1.74/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.74/1.02  
% 1.74/1.02  fof(f14,conjecture,(
% 1.74/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f15,negated_conjecture,(
% 1.74/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.74/1.02    inference(negated_conjecture,[],[f14])).
% 1.74/1.02  
% 1.74/1.02  fof(f37,plain,(
% 1.74/1.02    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.74/1.02    inference(ennf_transformation,[],[f15])).
% 1.74/1.02  
% 1.74/1.02  fof(f38,plain,(
% 1.74/1.02    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.74/1.02    inference(flattening,[],[f37])).
% 1.74/1.02  
% 1.74/1.02  fof(f40,plain,(
% 1.74/1.02    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.74/1.02    inference(nnf_transformation,[],[f38])).
% 1.74/1.02  
% 1.74/1.02  fof(f41,plain,(
% 1.74/1.02    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.74/1.02    inference(flattening,[],[f40])).
% 1.74/1.02  
% 1.74/1.02  fof(f44,plain,(
% 1.74/1.02    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & (r1_waybel_7(X0,X1,sK2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.74/1.02    introduced(choice_axiom,[])).
% 1.74/1.02  
% 1.74/1.02  fof(f43,plain,(
% 1.74/1.02    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & (r1_waybel_7(X0,sK1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK1))) )),
% 1.74/1.02    introduced(choice_axiom,[])).
% 1.74/1.02  
% 1.74/1.02  fof(f42,plain,(
% 1.74/1.02    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.74/1.02    introduced(choice_axiom,[])).
% 1.74/1.02  
% 1.74/1.02  fof(f45,plain,(
% 1.74/1.02    (((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.74/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43,f42])).
% 1.74/1.02  
% 1.74/1.02  fof(f68,plain,(
% 1.74/1.02    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.74/1.02    inference(cnf_transformation,[],[f45])).
% 1.74/1.02  
% 1.74/1.02  fof(f8,axiom,(
% 1.74/1.02    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f53,plain,(
% 1.74/1.02    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.74/1.02    inference(cnf_transformation,[],[f8])).
% 1.74/1.02  
% 1.74/1.02  fof(f83,plain,(
% 1.74/1.02    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.74/1.02    inference(definition_unfolding,[],[f68,f53])).
% 1.74/1.02  
% 1.74/1.02  fof(f69,plain,(
% 1.74/1.02    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.74/1.02    inference(cnf_transformation,[],[f45])).
% 1.74/1.02  
% 1.74/1.02  fof(f82,plain,(
% 1.74/1.02    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.74/1.02    inference(definition_unfolding,[],[f69,f53])).
% 1.74/1.02  
% 1.74/1.02  fof(f11,axiom,(
% 1.74/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f17,plain,(
% 1.74/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.74/1.02    inference(pure_predicate_removal,[],[f11])).
% 1.74/1.02  
% 1.74/1.02  fof(f31,plain,(
% 1.74/1.02    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.74/1.02    inference(ennf_transformation,[],[f17])).
% 1.74/1.02  
% 1.74/1.02  fof(f32,plain,(
% 1.74/1.02    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.74/1.02    inference(flattening,[],[f31])).
% 1.74/1.02  
% 1.74/1.02  fof(f59,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f32])).
% 1.74/1.02  
% 1.74/1.02  fof(f78,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(definition_unfolding,[],[f59,f53,f53,f53,f53])).
% 1.74/1.02  
% 1.74/1.02  fof(f67,plain,(
% 1.74/1.02    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.74/1.02    inference(cnf_transformation,[],[f45])).
% 1.74/1.02  
% 1.74/1.02  fof(f84,plain,(
% 1.74/1.02    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.74/1.02    inference(definition_unfolding,[],[f67,f53])).
% 1.74/1.02  
% 1.74/1.02  fof(f66,plain,(
% 1.74/1.02    ~v1_xboole_0(sK1)),
% 1.74/1.02    inference(cnf_transformation,[],[f45])).
% 1.74/1.02  
% 1.74/1.02  fof(f5,axiom,(
% 1.74/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f22,plain,(
% 1.74/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.74/1.02    inference(ennf_transformation,[],[f5])).
% 1.74/1.02  
% 1.74/1.02  fof(f50,plain,(
% 1.74/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f22])).
% 1.74/1.02  
% 1.74/1.02  fof(f65,plain,(
% 1.74/1.02    l1_pre_topc(sK0)),
% 1.74/1.02    inference(cnf_transformation,[],[f45])).
% 1.74/1.02  
% 1.74/1.02  fof(f63,plain,(
% 1.74/1.02    ~v2_struct_0(sK0)),
% 1.74/1.02    inference(cnf_transformation,[],[f45])).
% 1.74/1.02  
% 1.74/1.02  fof(f4,axiom,(
% 1.74/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f21,plain,(
% 1.74/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.74/1.02    inference(ennf_transformation,[],[f4])).
% 1.74/1.02  
% 1.74/1.02  fof(f49,plain,(
% 1.74/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f21])).
% 1.74/1.02  
% 1.74/1.02  fof(f70,plain,(
% 1.74/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.74/1.02    inference(cnf_transformation,[],[f45])).
% 1.74/1.02  
% 1.74/1.02  fof(f81,plain,(
% 1.74/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.74/1.02    inference(definition_unfolding,[],[f70,f53])).
% 1.74/1.02  
% 1.74/1.02  fof(f9,axiom,(
% 1.74/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f18,plain,(
% 1.74/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.74/1.02    inference(pure_predicate_removal,[],[f9])).
% 1.74/1.02  
% 1.74/1.02  fof(f27,plain,(
% 1.74/1.02    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.74/1.02    inference(ennf_transformation,[],[f18])).
% 1.74/1.02  
% 1.74/1.02  fof(f28,plain,(
% 1.74/1.02    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.74/1.02    inference(flattening,[],[f27])).
% 1.74/1.02  
% 1.74/1.02  fof(f55,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f28])).
% 1.74/1.02  
% 1.74/1.02  fof(f74,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(definition_unfolding,[],[f55,f53,f53,f53])).
% 1.74/1.02  
% 1.74/1.02  fof(f73,plain,(
% 1.74/1.02    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.74/1.02    inference(cnf_transformation,[],[f45])).
% 1.74/1.02  
% 1.74/1.02  fof(f12,axiom,(
% 1.74/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f33,plain,(
% 1.74/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/1.02    inference(ennf_transformation,[],[f12])).
% 1.74/1.02  
% 1.74/1.02  fof(f34,plain,(
% 1.74/1.02    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/1.02    inference(flattening,[],[f33])).
% 1.74/1.02  
% 1.74/1.02  fof(f39,plain,(
% 1.74/1.02    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/1.02    inference(nnf_transformation,[],[f34])).
% 1.74/1.02  
% 1.74/1.02  fof(f61,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f39])).
% 1.74/1.02  
% 1.74/1.02  fof(f64,plain,(
% 1.74/1.02    v2_pre_topc(sK0)),
% 1.74/1.02    inference(cnf_transformation,[],[f45])).
% 1.74/1.02  
% 1.74/1.02  fof(f71,plain,(
% 1.74/1.02    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.74/1.02    inference(cnf_transformation,[],[f45])).
% 1.74/1.02  
% 1.74/1.02  fof(f13,axiom,(
% 1.74/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f35,plain,(
% 1.74/1.02    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.74/1.02    inference(ennf_transformation,[],[f13])).
% 1.74/1.02  
% 1.74/1.02  fof(f36,plain,(
% 1.74/1.02    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.74/1.02    inference(flattening,[],[f35])).
% 1.74/1.02  
% 1.74/1.02  fof(f62,plain,(
% 1.74/1.02    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f36])).
% 1.74/1.02  
% 1.74/1.02  fof(f80,plain,(
% 1.74/1.02    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(definition_unfolding,[],[f62,f53,f53,f53,f53])).
% 1.74/1.02  
% 1.74/1.02  fof(f72,plain,(
% 1.74/1.02    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.74/1.02    inference(cnf_transformation,[],[f45])).
% 1.74/1.02  
% 1.74/1.02  fof(f60,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f39])).
% 1.74/1.02  
% 1.74/1.02  fof(f6,axiom,(
% 1.74/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f23,plain,(
% 1.74/1.02    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/1.02    inference(ennf_transformation,[],[f6])).
% 1.74/1.02  
% 1.74/1.02  fof(f24,plain,(
% 1.74/1.02    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/1.02    inference(flattening,[],[f23])).
% 1.74/1.02  
% 1.74/1.02  fof(f51,plain,(
% 1.74/1.02    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f24])).
% 1.74/1.02  
% 1.74/1.02  fof(f3,axiom,(
% 1.74/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f20,plain,(
% 1.74/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.74/1.02    inference(ennf_transformation,[],[f3])).
% 1.74/1.02  
% 1.74/1.02  fof(f48,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f20])).
% 1.74/1.02  
% 1.74/1.02  fof(f7,axiom,(
% 1.74/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f25,plain,(
% 1.74/1.02    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/1.02    inference(ennf_transformation,[],[f7])).
% 1.74/1.02  
% 1.74/1.02  fof(f26,plain,(
% 1.74/1.02    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/1.02    inference(flattening,[],[f25])).
% 1.74/1.02  
% 1.74/1.02  fof(f52,plain,(
% 1.74/1.02    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f26])).
% 1.74/1.02  
% 1.74/1.02  fof(f58,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f32])).
% 1.74/1.02  
% 1.74/1.02  fof(f79,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(definition_unfolding,[],[f58,f53,f53,f53,f53])).
% 1.74/1.02  
% 1.74/1.02  fof(f10,axiom,(
% 1.74/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f16,plain,(
% 1.74/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.74/1.02    inference(pure_predicate_removal,[],[f10])).
% 1.74/1.02  
% 1.74/1.02  fof(f19,plain,(
% 1.74/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.74/1.02    inference(pure_predicate_removal,[],[f16])).
% 1.74/1.02  
% 1.74/1.02  fof(f29,plain,(
% 1.74/1.02    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.74/1.02    inference(ennf_transformation,[],[f19])).
% 1.74/1.02  
% 1.74/1.02  fof(f30,plain,(
% 1.74/1.02    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.74/1.02    inference(flattening,[],[f29])).
% 1.74/1.02  
% 1.74/1.02  fof(f56,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f30])).
% 1.74/1.02  
% 1.74/1.02  fof(f77,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(definition_unfolding,[],[f56,f53,f53,f53])).
% 1.74/1.02  
% 1.74/1.02  fof(f2,axiom,(
% 1.74/1.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f47,plain,(
% 1.74/1.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.74/1.02    inference(cnf_transformation,[],[f2])).
% 1.74/1.02  
% 1.74/1.02  fof(f1,axiom,(
% 1.74/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 1.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.74/1.02  
% 1.74/1.02  fof(f46,plain,(
% 1.74/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.74/1.02    inference(cnf_transformation,[],[f1])).
% 1.74/1.02  
% 1.74/1.02  fof(f57,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(cnf_transformation,[],[f30])).
% 1.74/1.02  
% 1.74/1.02  fof(f76,plain,(
% 1.74/1.02    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.74/1.02    inference(definition_unfolding,[],[f57,f53,f53,f53])).
% 1.74/1.02  
% 1.74/1.02  cnf(c_21,negated_conjecture,
% 1.74/1.02      ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.74/1.02      inference(cnf_transformation,[],[f83]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_20,negated_conjecture,
% 1.74/1.02      ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.74/1.02      inference(cnf_transformation,[],[f82]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_11,plain,
% 1.74/1.02      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | ~ l1_struct_0(X2)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | v1_xboole_0(X1) ),
% 1.74/1.02      inference(cnf_transformation,[],[f78]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_22,negated_conjecture,
% 1.74/1.02      ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
% 1.74/1.02      inference(cnf_transformation,[],[f84]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_386,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | ~ l1_struct_0(X2)
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | sK1 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_387,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ l1_struct_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | v1_xboole_0(sK1)
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_386]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_23,negated_conjecture,
% 1.74/1.02      ( ~ v1_xboole_0(sK1) ),
% 1.74/1.02      inference(cnf_transformation,[],[f66]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_391,plain,
% 1.74/1.02      ( v1_xboole_0(X0)
% 1.74/1.02      | ~ l1_struct_0(X1)
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_387,c_23]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_392,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ l1_struct_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_391]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4,plain,
% 1.74/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.74/1.02      inference(cnf_transformation,[],[f50]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_24,negated_conjecture,
% 1.74/1.02      ( l1_pre_topc(sK0) ),
% 1.74/1.02      inference(cnf_transformation,[],[f65]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_604,plain,
% 1.74/1.02      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_605,plain,
% 1.74/1.02      ( l1_struct_0(sK0) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_604]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1420,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | sK0 != X1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_392,c_605]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1421,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v2_struct_0(sK0)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_1420]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_26,negated_conjecture,
% 1.74/1.02      ( ~ v2_struct_0(sK0) ),
% 1.74/1.02      inference(cnf_transformation,[],[f63]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1425,plain,
% 1.74/1.02      ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1421,c_26]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1426,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_1425]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1866,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | sK1 != sK1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_1426]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_2144,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | sK1 != sK1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_1866]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_3042,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_2144]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4107,plain,
% 1.74/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,X0,sK1)) = iProver_top
% 1.74/1.02      | v1_xboole_0(X0) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_3042]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_3,plain,
% 1.74/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.74/1.02      inference(cnf_transformation,[],[f49]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1342,plain,
% 1.74/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_605]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1343,plain,
% 1.74/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_1342]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4198,plain,
% 1.74/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,X0,sK1)) = iProver_top
% 1.74/1.02      | v1_xboole_0(X0) = iProver_top ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_4107,c_1343]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4705,plain,
% 1.74/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.74/1.02      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 1.74/1.02      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 1.74/1.02      inference(equality_resolution,[status(thm)],[c_4198]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4959,plain,
% 1.74/1.02      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 1.74/1.02      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 1.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_4705]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_19,negated_conjecture,
% 1.74/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
% 1.74/1.02      inference(cnf_transformation,[],[f81]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_34,plain,
% 1.74/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_7,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | ~ l1_struct_0(X2)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | v1_xboole_0(X1) ),
% 1.74/1.02      inference(cnf_transformation,[],[f74]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_16,negated_conjecture,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.74/1.02      inference(cnf_transformation,[],[f73]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_193,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.74/1.02      inference(prop_impl,[status(thm)],[c_16]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_13,plain,
% 1.74/1.02      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.74/1.02      | r3_waybel_9(X0,X1,X2)
% 1.74/1.02      | ~ l1_waybel_0(X1,X0)
% 1.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.74/1.02      | ~ v7_waybel_0(X1)
% 1.74/1.02      | ~ v4_orders_2(X1)
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ v2_pre_topc(X0)
% 1.74/1.02      | ~ l1_pre_topc(X0) ),
% 1.74/1.02      inference(cnf_transformation,[],[f61]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_25,negated_conjecture,
% 1.74/1.02      ( v2_pre_topc(sK0) ),
% 1.74/1.02      inference(cnf_transformation,[],[f64]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_509,plain,
% 1.74/1.02      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.74/1.02      | r3_waybel_9(X0,X1,X2)
% 1.74/1.02      | ~ l1_waybel_0(X1,X0)
% 1.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.74/1.02      | ~ v7_waybel_0(X1)
% 1.74/1.02      | ~ v4_orders_2(X1)
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ l1_pre_topc(X0)
% 1.74/1.02      | sK0 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_510,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.74/1.02      | r3_waybel_9(sK0,X0,X1)
% 1.74/1.02      | ~ l1_waybel_0(X0,sK0)
% 1.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.74/1.02      | ~ v7_waybel_0(X0)
% 1.74/1.02      | ~ v4_orders_2(X0)
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | v2_struct_0(sK0)
% 1.74/1.02      | ~ l1_pre_topc(sK0) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_509]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_514,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.74/1.02      | r3_waybel_9(sK0,X0,X1)
% 1.74/1.02      | ~ l1_waybel_0(X0,sK0)
% 1.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.74/1.02      | ~ v7_waybel_0(X0)
% 1.74/1.02      | ~ v4_orders_2(X0)
% 1.74/1.02      | v2_struct_0(X0) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_510,c_26,c_24]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_933,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ l1_waybel_0(X0,sK0)
% 1.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.74/1.02      | ~ v7_waybel_0(X0)
% 1.74/1.02      | ~ v4_orders_2(X0)
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 1.74/1.02      | sK2 != X1
% 1.74/1.02      | sK0 != sK0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_193,c_514]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_934,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.74/1.02      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_933]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_18,negated_conjecture,
% 1.74/1.02      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 1.74/1.02      inference(cnf_transformation,[],[f71]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_936,plain,
% 1.74/1.02      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_934,c_18]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_937,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_936]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_973,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ l1_struct_0(X2)
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 1.74/1.02      | sK0 != X2 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_937]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_974,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(sK0)
% 1.74/1.02      | ~ l1_struct_0(sK0)
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_973]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_70,plain,
% 1.74/1.02      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.74/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_978,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_974,c_26,c_24,c_70]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1821,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.74/1.02      | sK1 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_978,c_20]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1822,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | v1_xboole_0(sK1)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_1821]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1826,plain,
% 1.74/1.02      ( v1_xboole_0(X0)
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1822,c_23]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1827,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_1826]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_2170,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | sK1 != sK1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_1827]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_3038,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_2170]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_3805,plain,
% 1.74/1.02      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | sP0_iProver_split ),
% 1.74/1.02      inference(splitting,
% 1.74/1.02                [splitting(split),new_symbols(definition,[])],
% 1.74/1.02                [c_3038]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4108,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 1.74/1.02      | sP0_iProver_split = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_3805]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_15,plain,
% 1.74/1.02      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ l1_struct_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 1.74/1.02      inference(cnf_transformation,[],[f80]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_425,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ l1_struct_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.74/1.02      | sK1 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_22]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_426,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | ~ l1_struct_0(X0)
% 1.74/1.02      | v1_xboole_0(sK1)
% 1.74/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_425]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_430,plain,
% 1.74/1.02      ( ~ l1_struct_0(X0)
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.74/1.02      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.74/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_426,c_23]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_431,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | ~ l1_struct_0(X0)
% 1.74/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_430]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1331,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.74/1.02      | sK0 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_431,c_605]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1332,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.74/1.02      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.74/1.02      | v2_struct_0(sK0)
% 1.74/1.02      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_1331]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1334,plain,
% 1.74/1.02      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.74/1.02      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_1332,c_26,c_21,c_20,c_19]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_3046,plain,
% 1.74/1.02      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_1334]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4211,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 1.74/1.02      | sP0_iProver_split = iProver_top ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_4108,c_3046]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_17,negated_conjecture,
% 1.74/1.02      ( r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.74/1.02      inference(cnf_transformation,[],[f72]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_195,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.74/1.02      inference(prop_impl,[status(thm)],[c_17]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_14,plain,
% 1.74/1.02      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.74/1.02      | ~ r3_waybel_9(X0,X1,X2)
% 1.74/1.02      | ~ l1_waybel_0(X1,X0)
% 1.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.74/1.02      | ~ v7_waybel_0(X1)
% 1.74/1.02      | ~ v4_orders_2(X1)
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ v2_pre_topc(X0)
% 1.74/1.02      | ~ l1_pre_topc(X0) ),
% 1.74/1.02      inference(cnf_transformation,[],[f60]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_476,plain,
% 1.74/1.02      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.74/1.02      | ~ r3_waybel_9(X0,X1,X2)
% 1.74/1.02      | ~ l1_waybel_0(X1,X0)
% 1.74/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.74/1.02      | ~ v7_waybel_0(X1)
% 1.74/1.02      | ~ v4_orders_2(X1)
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ l1_pre_topc(X0)
% 1.74/1.02      | sK0 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_477,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.74/1.02      | ~ r3_waybel_9(sK0,X0,X1)
% 1.74/1.02      | ~ l1_waybel_0(X0,sK0)
% 1.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.74/1.02      | ~ v7_waybel_0(X0)
% 1.74/1.02      | ~ v4_orders_2(X0)
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | v2_struct_0(sK0)
% 1.74/1.02      | ~ l1_pre_topc(sK0) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_476]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_481,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.74/1.02      | ~ r3_waybel_9(sK0,X0,X1)
% 1.74/1.02      | ~ l1_waybel_0(X0,sK0)
% 1.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.74/1.02      | ~ v7_waybel_0(X0)
% 1.74/1.02      | ~ v4_orders_2(X0)
% 1.74/1.02      | v2_struct_0(X0) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_477,c_26,c_24]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_907,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ l1_waybel_0(X0,sK0)
% 1.74/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.74/1.02      | ~ v7_waybel_0(X0)
% 1.74/1.02      | ~ v4_orders_2(X0)
% 1.74/1.02      | v2_struct_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 1.74/1.02      | sK2 != X1
% 1.74/1.02      | sK0 != sK0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_195,c_481]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_908,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.74/1.02      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_907]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_910,plain,
% 1.74/1.02      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_908,c_18]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_911,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_910]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1021,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ l1_struct_0(X2)
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 1.74/1.02      | sK0 != X2 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_911]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1022,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(sK0)
% 1.74/1.02      | ~ l1_struct_0(sK0)
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_1021]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1026,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_1022,c_26,c_24,c_70]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1776,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.74/1.02      | sK1 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_1026,c_20]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1777,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | v1_xboole_0(sK1)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_1776]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1781,plain,
% 1.74/1.02      ( v1_xboole_0(X0)
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1777,c_23]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1782,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_1781]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_2208,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | sK1 != sK1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_1782]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_3034,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_2208]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_3806,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2)
% 1.74/1.02      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.74/1.02      | sP0_iProver_split ),
% 1.74/1.02      inference(splitting,
% 1.74/1.02                [splitting(split),new_symbols(definition,[])],
% 1.74/1.02                [c_3034]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4110,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
% 1.74/1.02      | r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 1.74/1.02      | sP0_iProver_split = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_3806]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4187,plain,
% 1.74/1.02      ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 1.74/1.02      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 1.74/1.02      | sP0_iProver_split = iProver_top ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_4110,c_3046]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4217,plain,
% 1.74/1.02      ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 1.74/1.02      | sP0_iProver_split = iProver_top ),
% 1.74/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4211,c_4187]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4119,plain,
% 1.74/1.02      ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4129,plain,
% 1.74/1.02      ( m1_subset_1(sK2,k2_struct_0(sK0)) = iProver_top ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_4119,c_1343]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_5,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.74/1.02      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ v2_pre_topc(X1)
% 1.74/1.02      | ~ l1_pre_topc(X1) ),
% 1.74/1.02      inference(cnf_transformation,[],[f51]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_563,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.74/1.02      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ l1_pre_topc(X1)
% 1.74/1.02      | sK0 != X1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_564,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.74/1.02      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | v2_struct_0(sK0)
% 1.74/1.02      | ~ l1_pre_topc(sK0) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_563]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_568,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.74/1.02      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_564,c_26,c_24]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4114,plain,
% 1.74/1.02      ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 1.74/1.02      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4139,plain,
% 1.74/1.02      ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
% 1.74/1.02      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_4114,c_1343]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_2,plain,
% 1.74/1.02      ( ~ r2_hidden(X0,X1)
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 1.74/1.02      | ~ v1_xboole_0(X2) ),
% 1.74/1.02      inference(cnf_transformation,[],[f48]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_6,plain,
% 1.74/1.02      ( r2_hidden(X0,k1_connsp_2(X1,X0))
% 1.74/1.02      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ v2_pre_topc(X1)
% 1.74/1.02      | ~ l1_pre_topc(X1) ),
% 1.74/1.02      inference(cnf_transformation,[],[f52]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_355,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.74/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ v2_pre_topc(X1)
% 1.74/1.02      | ~ l1_pre_topc(X1)
% 1.74/1.02      | ~ v1_xboole_0(X3)
% 1.74/1.02      | X0 != X4
% 1.74/1.02      | k1_connsp_2(X1,X0) != X2 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_6]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_356,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.74/1.02      | ~ m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(X2))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ v2_pre_topc(X1)
% 1.74/1.02      | ~ l1_pre_topc(X1)
% 1.74/1.02      | ~ v1_xboole_0(X2) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_355]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_542,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.74/1.02      | ~ m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(X2))
% 1.74/1.02      | v2_struct_0(X1)
% 1.74/1.02      | ~ l1_pre_topc(X1)
% 1.74/1.02      | ~ v1_xboole_0(X2)
% 1.74/1.02      | sK0 != X1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_356,c_25]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_543,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.74/1.02      | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1))
% 1.74/1.02      | v2_struct_0(sK0)
% 1.74/1.02      | ~ l1_pre_topc(sK0)
% 1.74/1.02      | ~ v1_xboole_0(X1) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_542]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_547,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.74/1.02      | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1))
% 1.74/1.02      | ~ v1_xboole_0(X1) ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_543,c_26,c_24]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4115,plain,
% 1.74/1.02      ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 1.74/1.02      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1)) != iProver_top
% 1.74/1.02      | v1_xboole_0(X1) != iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4144,plain,
% 1.74/1.02      ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
% 1.74/1.02      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1)) != iProver_top
% 1.74/1.02      | v1_xboole_0(X1) != iProver_top ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_4115,c_1343]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4370,plain,
% 1.74/1.02      ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
% 1.74/1.02      | v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
% 1.74/1.02      inference(superposition,[status(thm)],[c_4139,c_4144]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4764,plain,
% 1.74/1.02      ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
% 1.74/1.02      inference(superposition,[status(thm)],[c_4129,c_4370]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_12,plain,
% 1.74/1.02      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.74/1.02      | ~ l1_struct_0(X2)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | v1_xboole_0(X1) ),
% 1.74/1.02      inference(cnf_transformation,[],[f79]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_10,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.74/1.02      | ~ l1_struct_0(X2)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | v1_xboole_0(X1) ),
% 1.74/1.02      inference(cnf_transformation,[],[f77]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_149,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.74/1.02      | ~ l1_struct_0(X2)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | v1_xboole_0(X1) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_12,c_10]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_150,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.74/1.02      | ~ l1_struct_0(X2)
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_149]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1347,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | sK0 != X2 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_150,c_605]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1348,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.74/1.02      | v2_struct_0(sK0)
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_1347]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1352,plain,
% 1.74/1.02      ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1348,c_26]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1353,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_1352]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1746,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.74/1.02      | sK1 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_1353,c_20]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1747,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | v1_xboole_0(sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_1746]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1751,plain,
% 1.74/1.02      ( v1_xboole_0(X0)
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1747,c_23]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1752,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_1751]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_2246,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | sK1 != sK1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_1752]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_3030,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_2246]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4112,plain,
% 1.74/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,X0,sK1)) != iProver_top
% 1.74/1.02      | v1_xboole_0(X0) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_3030]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4162,plain,
% 1.74/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,X0,sK1)) != iProver_top
% 1.74/1.02      | v1_xboole_0(X0) = iProver_top ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_4112,c_1343]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4607,plain,
% 1.74/1.02      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 1.74/1.02      inference(equality_resolution,[status(thm)],[c_4162]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4793,plain,
% 1.74/1.02      ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 1.74/1.02      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_4607,c_34,c_4764]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4794,plain,
% 1.74/1.02      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_4793]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1,plain,
% 1.74/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.74/1.02      inference(cnf_transformation,[],[f47]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4120,plain,
% 1.74/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_0,plain,
% 1.74/1.02      ( k2_subset_1(X0) = X0 ),
% 1.74/1.02      inference(cnf_transformation,[],[f46]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4132,plain,
% 1.74/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_4120,c_0]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4799,plain,
% 1.74/1.02      ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
% 1.74/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4794,c_4132]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_3804,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | ~ sP0_iProver_split ),
% 1.74/1.02      inference(splitting,
% 1.74/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.74/1.02                [c_3038]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4109,plain,
% 1.74/1.02      ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.74/1.02      | v1_xboole_0(X0) = iProver_top
% 1.74/1.02      | sP0_iProver_split != iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_3804]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4173,plain,
% 1.74/1.02      ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.74/1.02      | v1_xboole_0(X0) = iProver_top
% 1.74/1.02      | sP0_iProver_split != iProver_top ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_4109,c_1343]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4696,plain,
% 1.74/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.74/1.02      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.74/1.02      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
% 1.74/1.02      | sP0_iProver_split != iProver_top ),
% 1.74/1.02      inference(equality_resolution,[status(thm)],[c_4173]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4801,plain,
% 1.74/1.02      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.74/1.02      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
% 1.74/1.02      | sP0_iProver_split != iProver_top ),
% 1.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_4696]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4803,plain,
% 1.74/1.02      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | sP0_iProver_split != iProver_top ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_4801,c_34,c_4764]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4809,plain,
% 1.74/1.02      ( sP0_iProver_split != iProver_top ),
% 1.74/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4803,c_4132]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_9,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | ~ l1_struct_0(X2)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | v1_xboole_0(X1) ),
% 1.74/1.02      inference(cnf_transformation,[],[f76]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1380,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.74/1.02      | v2_struct_0(X2)
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | sK0 != X2 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_605]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1381,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.74/1.02      | v2_struct_0(sK0)
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_1380]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1385,plain,
% 1.74/1.02      ( v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1381,c_26]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1386,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_1385]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1716,plain,
% 1.74/1.02      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.74/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.74/1.02      | v1_xboole_0(X1)
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.74/1.02      | sK1 != X0 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_1386,c_20]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1717,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | v1_xboole_0(sK1)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(unflattening,[status(thm)],[c_1716]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1721,plain,
% 1.74/1.02      ( v1_xboole_0(X0)
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1717,c_23]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_1722,plain,
% 1.74/1.02      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.74/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_1721]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_2269,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | sK1 != sK1 ),
% 1.74/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_1722]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_3026,plain,
% 1.74/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.74/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.74/1.02      | v1_xboole_0(X0)
% 1.74/1.02      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_2269]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4113,plain,
% 1.74/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,X0,sK1)) = iProver_top
% 1.74/1.02      | v1_xboole_0(X0) = iProver_top ),
% 1.74/1.02      inference(predicate_to_equality,[status(thm)],[c_3026]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4151,plain,
% 1.74/1.02      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.74/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,X0,sK1)) = iProver_top
% 1.74/1.02      | v1_xboole_0(X0) = iProver_top ),
% 1.74/1.02      inference(light_normalisation,[status(thm)],[c_4113,c_1343]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4599,plain,
% 1.74/1.02      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 1.74/1.02      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 1.74/1.02      inference(equality_resolution,[status(thm)],[c_4151]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4872,plain,
% 1.74/1.02      ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 1.74/1.02      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_4599,c_34,c_4764]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4873,plain,
% 1.74/1.02      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 1.74/1.02      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
% 1.74/1.02      inference(renaming,[status(thm)],[c_4872]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4878,plain,
% 1.74/1.02      ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
% 1.74/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4873,c_4132]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4961,plain,
% 1.74/1.02      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 1.74/1.02      inference(global_propositional_subsumption,
% 1.74/1.02                [status(thm)],
% 1.74/1.02                [c_4959,c_34,c_4217,c_4764,c_4799,c_4809,c_4878]) ).
% 1.74/1.02  
% 1.74/1.02  cnf(c_4966,plain,
% 1.74/1.02      ( $false ),
% 1.74/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4961,c_4132]) ).
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 1.74/1.02  
% 1.74/1.02  ------                               Statistics
% 1.74/1.02  
% 1.74/1.02  ------ General
% 1.74/1.02  
% 1.74/1.02  abstr_ref_over_cycles:                  0
% 1.74/1.02  abstr_ref_under_cycles:                 0
% 1.74/1.02  gc_basic_clause_elim:                   0
% 1.74/1.02  forced_gc_time:                         0
% 1.74/1.02  parsing_time:                           0.011
% 1.74/1.02  unif_index_cands_time:                  0.
% 1.74/1.02  unif_index_add_time:                    0.
% 1.74/1.02  orderings_time:                         0.
% 1.74/1.02  out_proof_time:                         0.016
% 1.74/1.02  total_time:                             0.18
% 1.74/1.02  num_of_symbols:                         59
% 1.74/1.02  num_of_terms:                           2124
% 1.74/1.02  
% 1.74/1.02  ------ Preprocessing
% 1.74/1.02  
% 1.74/1.02  num_of_splits:                          2
% 1.74/1.02  num_of_split_atoms:                     1
% 1.74/1.02  num_of_reused_defs:                     1
% 1.74/1.02  num_eq_ax_congr_red:                    11
% 1.74/1.02  num_of_sem_filtered_clauses:            1
% 1.74/1.02  num_of_subtypes:                        0
% 1.74/1.02  monotx_restored_types:                  0
% 1.74/1.02  sat_num_of_epr_types:                   0
% 1.74/1.02  sat_num_of_non_cyclic_types:            0
% 1.74/1.02  sat_guarded_non_collapsed_types:        0
% 1.74/1.02  num_pure_diseq_elim:                    0
% 1.74/1.02  simp_replaced_by:                       0
% 1.74/1.02  res_preprocessed:                       106
% 1.74/1.02  prep_upred:                             0
% 1.74/1.02  prep_unflattend:                        53
% 1.74/1.02  smt_new_axioms:                         0
% 1.74/1.02  pred_elim_cands:                        6
% 1.74/1.02  pred_elim:                              9
% 1.74/1.02  pred_elim_cl:                           11
% 1.74/1.02  pred_elim_cycles:                       26
% 1.74/1.02  merged_defs:                            2
% 1.74/1.02  merged_defs_ncl:                        0
% 1.74/1.02  bin_hyper_res:                          2
% 1.74/1.02  prep_cycles:                            4
% 1.74/1.02  pred_elim_time:                         0.093
% 1.74/1.02  splitting_time:                         0.
% 1.74/1.02  sem_filter_time:                        0.
% 1.74/1.02  monotx_time:                            0.
% 1.74/1.02  subtype_inf_time:                       0.
% 1.74/1.02  
% 1.74/1.02  ------ Problem properties
% 1.74/1.02  
% 1.74/1.02  clauses:                                17
% 1.74/1.02  conjectures:                            4
% 1.74/1.02  epr:                                    2
% 1.74/1.02  horn:                                   13
% 1.74/1.02  ground:                                 8
% 1.74/1.02  unary:                                  8
% 1.74/1.02  binary:                                 1
% 1.74/1.02  lits:                                   53
% 1.74/1.02  lits_eq:                                11
% 1.74/1.02  fd_pure:                                0
% 1.74/1.02  fd_pseudo:                              0
% 1.74/1.02  fd_cond:                                0
% 1.74/1.02  fd_pseudo_cond:                         0
% 1.74/1.02  ac_symbols:                             0
% 1.74/1.02  
% 1.74/1.02  ------ Propositional Solver
% 1.74/1.02  
% 1.74/1.02  prop_solver_calls:                      27
% 1.74/1.02  prop_fast_solver_calls:                 1820
% 1.74/1.02  smt_solver_calls:                       0
% 1.74/1.02  smt_fast_solver_calls:                  0
% 1.74/1.02  prop_num_of_clauses:                    886
% 1.74/1.02  prop_preprocess_simplified:             3229
% 1.74/1.02  prop_fo_subsumed:                       45
% 1.74/1.02  prop_solver_time:                       0.
% 1.74/1.02  smt_solver_time:                        0.
% 1.74/1.02  smt_fast_solver_time:                   0.
% 1.74/1.02  prop_fast_solver_time:                  0.
% 1.74/1.02  prop_unsat_core_time:                   0.
% 1.74/1.02  
% 1.74/1.02  ------ QBF
% 1.74/1.02  
% 1.74/1.02  qbf_q_res:                              0
% 1.74/1.02  qbf_num_tautologies:                    0
% 1.74/1.02  qbf_prep_cycles:                        0
% 1.74/1.02  
% 1.74/1.02  ------ BMC1
% 1.74/1.02  
% 1.74/1.02  bmc1_current_bound:                     -1
% 1.74/1.02  bmc1_last_solved_bound:                 -1
% 1.74/1.02  bmc1_unsat_core_size:                   -1
% 1.74/1.02  bmc1_unsat_core_parents_size:           -1
% 1.74/1.02  bmc1_merge_next_fun:                    0
% 1.74/1.02  bmc1_unsat_core_clauses_time:           0.
% 1.74/1.02  
% 1.74/1.02  ------ Instantiation
% 1.74/1.02  
% 1.74/1.02  inst_num_of_clauses:                    176
% 1.74/1.02  inst_num_in_passive:                    31
% 1.74/1.02  inst_num_in_active:                     115
% 1.74/1.02  inst_num_in_unprocessed:                30
% 1.74/1.02  inst_num_of_loops:                      120
% 1.74/1.02  inst_num_of_learning_restarts:          0
% 1.74/1.02  inst_num_moves_active_passive:          2
% 1.74/1.02  inst_lit_activity:                      0
% 1.74/1.02  inst_lit_activity_moves:                0
% 1.74/1.02  inst_num_tautologies:                   0
% 1.74/1.02  inst_num_prop_implied:                  0
% 1.74/1.02  inst_num_existing_simplified:           0
% 1.74/1.02  inst_num_eq_res_simplified:             0
% 1.74/1.02  inst_num_child_elim:                    0
% 1.74/1.02  inst_num_of_dismatching_blockings:      38
% 1.74/1.02  inst_num_of_non_proper_insts:           117
% 1.74/1.02  inst_num_of_duplicates:                 0
% 1.74/1.02  inst_inst_num_from_inst_to_res:         0
% 1.74/1.02  inst_dismatching_checking_time:         0.
% 1.74/1.02  
% 1.74/1.02  ------ Resolution
% 1.74/1.02  
% 1.74/1.02  res_num_of_clauses:                     0
% 1.74/1.02  res_num_in_passive:                     0
% 1.74/1.02  res_num_in_active:                      0
% 1.74/1.02  res_num_of_loops:                       110
% 1.74/1.02  res_forward_subset_subsumed:            8
% 1.74/1.02  res_backward_subset_subsumed:           0
% 1.74/1.02  res_forward_subsumed:                   1
% 1.74/1.02  res_backward_subsumed:                  0
% 1.74/1.02  res_forward_subsumption_resolution:     2
% 1.74/1.02  res_backward_subsumption_resolution:    0
% 1.74/1.02  res_clause_to_clause_subsumption:       295
% 1.74/1.02  res_orphan_elimination:                 0
% 1.74/1.02  res_tautology_del:                      21
% 1.74/1.02  res_num_eq_res_simplified:              6
% 1.74/1.02  res_num_sel_changes:                    0
% 1.74/1.02  res_moves_from_active_to_pass:          0
% 1.74/1.02  
% 1.74/1.02  ------ Superposition
% 1.74/1.02  
% 1.74/1.02  sup_time_total:                         0.
% 1.74/1.02  sup_time_generating:                    0.
% 1.74/1.02  sup_time_sim_full:                      0.
% 1.74/1.02  sup_time_sim_immed:                     0.
% 1.74/1.02  
% 1.74/1.02  sup_num_of_clauses:                     22
% 1.74/1.02  sup_num_in_active:                      22
% 1.74/1.02  sup_num_in_passive:                     0
% 1.74/1.02  sup_num_of_loops:                       22
% 1.74/1.02  sup_fw_superposition:                   3
% 1.74/1.02  sup_bw_superposition:                   1
% 1.74/1.02  sup_immediate_simplified:               0
% 1.74/1.02  sup_given_eliminated:                   0
% 1.74/1.02  comparisons_done:                       0
% 1.74/1.02  comparisons_avoided:                    0
% 1.74/1.02  
% 1.74/1.02  ------ Simplifications
% 1.74/1.02  
% 1.74/1.02  
% 1.74/1.02  sim_fw_subset_subsumed:                 0
% 1.74/1.02  sim_bw_subset_subsumed:                 0
% 1.74/1.02  sim_fw_subsumed:                        0
% 1.74/1.02  sim_bw_subsumed:                        1
% 1.74/1.02  sim_fw_subsumption_res:                 5
% 1.74/1.02  sim_bw_subsumption_res:                 0
% 1.74/1.02  sim_tautology_del:                      0
% 1.74/1.02  sim_eq_tautology_del:                   0
% 1.74/1.02  sim_eq_res_simp:                        2
% 1.74/1.02  sim_fw_demodulated:                     0
% 1.74/1.02  sim_bw_demodulated:                     0
% 1.74/1.02  sim_light_normalised:                   11
% 1.74/1.02  sim_joinable_taut:                      0
% 1.74/1.02  sim_joinable_simp:                      0
% 1.74/1.02  sim_ac_normalised:                      0
% 1.74/1.02  sim_smt_subsumption:                    0
% 1.74/1.02  
%------------------------------------------------------------------------------
