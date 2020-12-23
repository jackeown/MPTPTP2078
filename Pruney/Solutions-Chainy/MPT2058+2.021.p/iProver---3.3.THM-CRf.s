%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:19 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3111)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).

fof(f57,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f57,f42])).

fof(f58,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f58,f42])).

fof(f7,axiom,(
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

fof(f14,plain,(
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
    inference(pure_predicate_removal,[],[f7])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
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
    inference(definition_unfolding,[],[f48,f42,f42,f42,f42])).

fof(f56,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f56,f42])).

fof(f55,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f59,f42])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
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
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
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
    inference(definition_unfolding,[],[f44,f42,f42,f42])).

fof(f62,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
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
    inference(definition_unfolding,[],[f43,f42,f42,f42])).

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
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(pure_predicate_removal,[],[f6])).

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
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
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
    inference(definition_unfolding,[],[f46,f42,f42,f42])).

fof(f9,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f51,f42,f42,f42,f42])).

fof(f61,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f32])).

cnf(c_17,negated_conjecture,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_16,negated_conjecture,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_18,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_306,plain,
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
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_307,plain,
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
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_19,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_311,plain,
    ( v1_xboole_0(X0)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_307,c_19])).

cnf(c_312,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_478,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_479,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_1040,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_312,c_479])).

cnf(c_1041,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1040])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1045,plain,
    ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1041,c_22])).

cnf(c_1046,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1045])).

cnf(c_1489,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_1046])).

cnf(c_1767,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1489])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_956,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_479])).

cnf(c_957,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_956])).

cnf(c_60,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_63,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_959,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_957,c_22,c_20,c_60,c_63])).

cnf(c_2508,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | k2_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1767,c_959])).

cnf(c_2509,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_2508])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_0,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_66,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2511,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2509,c_20,c_15,c_63,c_66])).

cnf(c_3106,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2511])).

cnf(c_3,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_12,negated_conjecture,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_166,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_429,plain,
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
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_430,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_434,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_22,c_20])).

cnf(c_807,plain,
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
    inference(resolution_lifted,[status(thm)],[c_166,c_434])).

cnf(c_808,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_807])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_810,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_808,c_14])).

cnf(c_811,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_810])).

cnf(c_847,plain,
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
    inference(resolution_lifted,[status(thm)],[c_3,c_811])).

cnf(c_848,plain,
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
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_852,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_848,c_22,c_20,c_63])).

cnf(c_853,plain,
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
    inference(renaming,[status(thm)],[c_852])).

cnf(c_1444,plain,
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
    inference(resolution_lifted,[status(thm)],[c_853,c_16])).

cnf(c_1445,plain,
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
    inference(unflattening,[status(thm)],[c_1444])).

cnf(c_1449,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1445,c_19])).

cnf(c_1450,plain,
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
    inference(renaming,[status(thm)],[c_1449])).

cnf(c_1793,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_1450])).

cnf(c_2485,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | k2_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1793,c_959])).

cnf(c_2486,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2485])).

cnf(c_4,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1007,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_479])).

cnf(c_1008,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1007])).

cnf(c_1012,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1008,c_22])).

cnf(c_1013,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1012])).

cnf(c_1339,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1013,c_16])).

cnf(c_1340,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1339])).

cnf(c_1344,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1340,c_19])).

cnf(c_1345,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1344])).

cnf(c_1892,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1345])).

cnf(c_2434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | k2_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1892,c_959])).

cnf(c_2435,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2434])).

cnf(c_2437,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2435,c_20,c_15,c_63,c_66])).

cnf(c_5,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_974,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_479])).

cnf(c_975,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_974])).

cnf(c_979,plain,
    ( v4_orders_2(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_975,c_22])).

cnf(c_980,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_979])).

cnf(c_1369,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_980,c_16])).

cnf(c_1370,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1369])).

cnf(c_1374,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1370,c_19])).

cnf(c_1375,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1374])).

cnf(c_1869,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_1375])).

cnf(c_2448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | k2_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1869,c_959])).

cnf(c_2449,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2448])).

cnf(c_2451,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2449,c_20,c_15,c_63,c_66])).

cnf(c_2488,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2486,c_20,c_15,c_63,c_66,c_2437,c_2451])).

cnf(c_3108,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2488])).

cnf(c_3197,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
    inference(prop_impl,[status(thm)],[c_3111])).

cnf(c_3198,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_3197])).

cnf(c_3223,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_3198])).

cnf(c_3327,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
    | r1_waybel_7(sK0,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3223])).

cnf(c_11,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_345,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_346,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | v1_xboole_0(sK1)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_350,plain,
    ( v2_struct_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_19])).

cnf(c_351,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(renaming,[status(thm)],[c_350])).

cnf(c_945,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_351,c_479])).

cnf(c_946,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_945])).

cnf(c_948,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_946,c_22,c_17,c_16,c_15])).

cnf(c_3122,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_948])).

cnf(c_3221,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_3122])).

cnf(c_3334,plain,
    ( r1_waybel_7(sK0,sK1,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3327,c_3221])).

cnf(c_13,negated_conjecture,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_168,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f49])).

cnf(c_396,plain,
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
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_397,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_401,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_22,c_20])).

cnf(c_781,plain,
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
    inference(resolution_lifted,[status(thm)],[c_168,c_401])).

cnf(c_782,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_784,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,sK1,sK2)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_782,c_14])).

cnf(c_785,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_784])).

cnf(c_895,plain,
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
    inference(resolution_lifted,[status(thm)],[c_3,c_785])).

cnf(c_896,plain,
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
    inference(unflattening,[status(thm)],[c_895])).

cnf(c_900,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_896,c_22,c_20,c_63])).

cnf(c_901,plain,
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
    inference(renaming,[status(thm)],[c_900])).

cnf(c_1399,plain,
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
    inference(resolution_lifted,[status(thm)],[c_901,c_16])).

cnf(c_1400,plain,
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
    inference(unflattening,[status(thm)],[c_1399])).

cnf(c_1404,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1400,c_19])).

cnf(c_1405,plain,
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
    inference(renaming,[status(thm)],[c_1404])).

cnf(c_1831,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_1405])).

cnf(c_2462,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | k2_struct_0(sK0) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_1831,c_959])).

cnf(c_2463,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_2462])).

cnf(c_2465,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2463,c_20,c_15,c_63,c_66,c_2437,c_2451])).

cnf(c_3114,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2465])).

cnf(c_3199,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
    inference(prop_impl,[status(thm)],[c_3117])).

cnf(c_3200,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(renaming,[status(thm)],[c_3199])).

cnf(c_3222,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_3200])).

cnf(c_3328,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3222])).

cnf(c_3331,plain,
    ( r1_waybel_7(sK0,sK1,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3328,c_3221])).

cnf(c_3336,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3334,c_3331])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:35:21 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 1.53/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/0.97  
% 1.53/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.53/0.97  
% 1.53/0.97  ------  iProver source info
% 1.53/0.97  
% 1.53/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.53/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.53/0.97  git: non_committed_changes: false
% 1.53/0.97  git: last_make_outside_of_git: false
% 1.53/0.97  
% 1.53/0.97  ------ 
% 1.53/0.97  
% 1.53/0.97  ------ Input Options
% 1.53/0.97  
% 1.53/0.97  --out_options                           all
% 1.53/0.97  --tptp_safe_out                         true
% 1.53/0.97  --problem_path                          ""
% 1.53/0.97  --include_path                          ""
% 1.53/0.97  --clausifier                            res/vclausify_rel
% 1.53/0.97  --clausifier_options                    --mode clausify
% 1.53/0.97  --stdin                                 false
% 1.53/0.97  --stats_out                             all
% 1.53/0.97  
% 1.53/0.97  ------ General Options
% 1.53/0.97  
% 1.53/0.97  --fof                                   false
% 1.53/0.97  --time_out_real                         305.
% 1.53/0.97  --time_out_virtual                      -1.
% 1.53/0.97  --symbol_type_check                     false
% 1.53/0.97  --clausify_out                          false
% 1.53/0.97  --sig_cnt_out                           false
% 1.53/0.97  --trig_cnt_out                          false
% 1.53/0.97  --trig_cnt_out_tolerance                1.
% 1.53/0.97  --trig_cnt_out_sk_spl                   false
% 1.53/0.97  --abstr_cl_out                          false
% 1.53/0.97  
% 1.53/0.97  ------ Global Options
% 1.53/0.97  
% 1.53/0.97  --schedule                              default
% 1.53/0.97  --add_important_lit                     false
% 1.53/0.97  --prop_solver_per_cl                    1000
% 1.53/0.97  --min_unsat_core                        false
% 1.53/0.97  --soft_assumptions                      false
% 1.53/0.97  --soft_lemma_size                       3
% 1.53/0.97  --prop_impl_unit_size                   0
% 1.53/0.97  --prop_impl_unit                        []
% 1.53/0.97  --share_sel_clauses                     true
% 1.53/0.97  --reset_solvers                         false
% 1.53/0.97  --bc_imp_inh                            [conj_cone]
% 1.53/0.97  --conj_cone_tolerance                   3.
% 1.53/0.97  --extra_neg_conj                        none
% 1.53/0.97  --large_theory_mode                     true
% 1.53/0.97  --prolific_symb_bound                   200
% 1.53/0.97  --lt_threshold                          2000
% 1.53/0.97  --clause_weak_htbl                      true
% 1.53/0.97  --gc_record_bc_elim                     false
% 1.53/0.97  
% 1.53/0.97  ------ Preprocessing Options
% 1.53/0.97  
% 1.53/0.97  --preprocessing_flag                    true
% 1.53/0.97  --time_out_prep_mult                    0.1
% 1.53/0.97  --splitting_mode                        input
% 1.53/0.97  --splitting_grd                         true
% 1.53/0.97  --splitting_cvd                         false
% 1.53/0.97  --splitting_cvd_svl                     false
% 1.53/0.97  --splitting_nvd                         32
% 1.53/0.97  --sub_typing                            true
% 1.53/0.97  --prep_gs_sim                           true
% 1.53/0.97  --prep_unflatten                        true
% 1.53/0.97  --prep_res_sim                          true
% 1.53/0.97  --prep_upred                            true
% 1.53/0.97  --prep_sem_filter                       exhaustive
% 1.53/0.97  --prep_sem_filter_out                   false
% 1.53/0.97  --pred_elim                             true
% 1.53/0.97  --res_sim_input                         true
% 1.53/0.97  --eq_ax_congr_red                       true
% 1.53/0.97  --pure_diseq_elim                       true
% 1.53/0.97  --brand_transform                       false
% 1.53/0.97  --non_eq_to_eq                          false
% 1.53/0.97  --prep_def_merge                        true
% 1.53/0.97  --prep_def_merge_prop_impl              false
% 1.53/0.97  --prep_def_merge_mbd                    true
% 1.53/0.97  --prep_def_merge_tr_red                 false
% 1.53/0.97  --prep_def_merge_tr_cl                  false
% 1.53/0.97  --smt_preprocessing                     true
% 1.53/0.97  --smt_ac_axioms                         fast
% 1.53/0.97  --preprocessed_out                      false
% 1.53/0.97  --preprocessed_stats                    false
% 1.53/0.97  
% 1.53/0.97  ------ Abstraction refinement Options
% 1.53/0.97  
% 1.53/0.97  --abstr_ref                             []
% 1.53/0.97  --abstr_ref_prep                        false
% 1.53/0.97  --abstr_ref_until_sat                   false
% 1.53/0.97  --abstr_ref_sig_restrict                funpre
% 1.53/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/0.97  --abstr_ref_under                       []
% 1.53/0.97  
% 1.53/0.97  ------ SAT Options
% 1.53/0.97  
% 1.53/0.97  --sat_mode                              false
% 1.53/0.97  --sat_fm_restart_options                ""
% 1.53/0.97  --sat_gr_def                            false
% 1.53/0.97  --sat_epr_types                         true
% 1.53/0.97  --sat_non_cyclic_types                  false
% 1.53/0.97  --sat_finite_models                     false
% 1.53/0.97  --sat_fm_lemmas                         false
% 1.53/0.97  --sat_fm_prep                           false
% 1.53/0.97  --sat_fm_uc_incr                        true
% 1.53/0.97  --sat_out_model                         small
% 1.53/0.97  --sat_out_clauses                       false
% 1.53/0.97  
% 1.53/0.97  ------ QBF Options
% 1.53/0.97  
% 1.53/0.97  --qbf_mode                              false
% 1.53/0.97  --qbf_elim_univ                         false
% 1.53/0.97  --qbf_dom_inst                          none
% 1.53/0.97  --qbf_dom_pre_inst                      false
% 1.53/0.97  --qbf_sk_in                             false
% 1.53/0.97  --qbf_pred_elim                         true
% 1.53/0.97  --qbf_split                             512
% 1.53/0.97  
% 1.53/0.97  ------ BMC1 Options
% 1.53/0.97  
% 1.53/0.97  --bmc1_incremental                      false
% 1.53/0.97  --bmc1_axioms                           reachable_all
% 1.53/0.97  --bmc1_min_bound                        0
% 1.53/0.97  --bmc1_max_bound                        -1
% 1.53/0.97  --bmc1_max_bound_default                -1
% 1.53/0.97  --bmc1_symbol_reachability              true
% 1.53/0.97  --bmc1_property_lemmas                  false
% 1.53/0.97  --bmc1_k_induction                      false
% 1.53/0.97  --bmc1_non_equiv_states                 false
% 1.53/0.97  --bmc1_deadlock                         false
% 1.53/0.97  --bmc1_ucm                              false
% 1.53/0.97  --bmc1_add_unsat_core                   none
% 1.53/0.97  --bmc1_unsat_core_children              false
% 1.53/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/0.97  --bmc1_out_stat                         full
% 1.53/0.97  --bmc1_ground_init                      false
% 1.53/0.97  --bmc1_pre_inst_next_state              false
% 1.53/0.97  --bmc1_pre_inst_state                   false
% 1.53/0.97  --bmc1_pre_inst_reach_state             false
% 1.53/0.97  --bmc1_out_unsat_core                   false
% 1.53/0.97  --bmc1_aig_witness_out                  false
% 1.53/0.97  --bmc1_verbose                          false
% 1.53/0.97  --bmc1_dump_clauses_tptp                false
% 1.53/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.53/0.97  --bmc1_dump_file                        -
% 1.53/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.53/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.53/0.97  --bmc1_ucm_extend_mode                  1
% 1.53/0.97  --bmc1_ucm_init_mode                    2
% 1.53/0.97  --bmc1_ucm_cone_mode                    none
% 1.53/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.53/0.97  --bmc1_ucm_relax_model                  4
% 1.53/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.53/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/0.97  --bmc1_ucm_layered_model                none
% 1.53/0.97  --bmc1_ucm_max_lemma_size               10
% 1.53/0.97  
% 1.53/0.97  ------ AIG Options
% 1.53/0.97  
% 1.53/0.97  --aig_mode                              false
% 1.53/0.97  
% 1.53/0.97  ------ Instantiation Options
% 1.53/0.97  
% 1.53/0.97  --instantiation_flag                    true
% 1.53/0.97  --inst_sos_flag                         false
% 1.53/0.97  --inst_sos_phase                        true
% 1.53/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/0.97  --inst_lit_sel_side                     num_symb
% 1.53/0.97  --inst_solver_per_active                1400
% 1.53/0.97  --inst_solver_calls_frac                1.
% 1.53/0.97  --inst_passive_queue_type               priority_queues
% 1.53/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.53/0.97  --inst_passive_queues_freq              [25;2]
% 1.53/0.97  --inst_dismatching                      true
% 1.53/0.97  --inst_eager_unprocessed_to_passive     true
% 1.53/0.97  --inst_prop_sim_given                   true
% 1.53/0.97  --inst_prop_sim_new                     false
% 1.53/0.97  --inst_subs_new                         false
% 1.53/0.97  --inst_eq_res_simp                      false
% 1.53/0.97  --inst_subs_given                       false
% 1.53/0.97  --inst_orphan_elimination               true
% 1.53/0.97  --inst_learning_loop_flag               true
% 1.53/0.97  --inst_learning_start                   3000
% 1.53/0.97  --inst_learning_factor                  2
% 1.53/0.97  --inst_start_prop_sim_after_learn       3
% 1.53/0.97  --inst_sel_renew                        solver
% 1.53/0.97  --inst_lit_activity_flag                true
% 1.53/0.97  --inst_restr_to_given                   false
% 1.53/0.97  --inst_activity_threshold               500
% 1.53/0.97  --inst_out_proof                        true
% 1.53/0.97  
% 1.53/0.97  ------ Resolution Options
% 1.53/0.97  
% 1.53/0.97  --resolution_flag                       true
% 1.53/0.97  --res_lit_sel                           adaptive
% 1.53/0.97  --res_lit_sel_side                      none
% 1.53/0.97  --res_ordering                          kbo
% 1.53/0.97  --res_to_prop_solver                    active
% 1.53/0.97  --res_prop_simpl_new                    false
% 1.53/0.97  --res_prop_simpl_given                  true
% 1.53/0.97  --res_passive_queue_type                priority_queues
% 1.53/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.53/0.97  --res_passive_queues_freq               [15;5]
% 1.53/0.97  --res_forward_subs                      full
% 1.53/0.97  --res_backward_subs                     full
% 1.53/0.97  --res_forward_subs_resolution           true
% 1.53/0.97  --res_backward_subs_resolution          true
% 1.53/0.97  --res_orphan_elimination                true
% 1.53/0.97  --res_time_limit                        2.
% 1.53/0.97  --res_out_proof                         true
% 1.53/0.97  
% 1.53/0.97  ------ Superposition Options
% 1.53/0.97  
% 1.53/0.97  --superposition_flag                    true
% 1.53/0.97  --sup_passive_queue_type                priority_queues
% 1.53/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.53/0.97  --demod_completeness_check              fast
% 1.53/0.97  --demod_use_ground                      true
% 1.53/0.97  --sup_to_prop_solver                    passive
% 1.53/0.97  --sup_prop_simpl_new                    true
% 1.53/0.97  --sup_prop_simpl_given                  true
% 1.53/0.97  --sup_fun_splitting                     false
% 1.53/0.97  --sup_smt_interval                      50000
% 1.53/0.97  
% 1.53/0.97  ------ Superposition Simplification Setup
% 1.53/0.97  
% 1.53/0.97  --sup_indices_passive                   []
% 1.53/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.53/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.97  --sup_full_bw                           [BwDemod]
% 1.53/0.97  --sup_immed_triv                        [TrivRules]
% 1.53/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.97  --sup_immed_bw_main                     []
% 1.53/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.97  
% 1.53/0.97  ------ Combination Options
% 1.53/0.97  
% 1.53/0.97  --comb_res_mult                         3
% 1.53/0.97  --comb_sup_mult                         2
% 1.53/0.97  --comb_inst_mult                        10
% 1.53/0.97  
% 1.53/0.97  ------ Debug Options
% 1.53/0.97  
% 1.53/0.97  --dbg_backtrace                         false
% 1.53/0.97  --dbg_dump_prop_clauses                 false
% 1.53/0.97  --dbg_dump_prop_clauses_file            -
% 1.53/0.97  --dbg_out_stat                          false
% 1.53/0.97  ------ Parsing...
% 1.53/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.53/0.97  
% 1.53/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 18 0s  sf_e  pe_s  pe_e  sf_s  rm: 13 0s  sf_e  pe_s  pe_e 
% 1.53/0.97  
% 1.53/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.53/0.97  
% 1.53/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.53/0.97  ------ Proving...
% 1.53/0.97  ------ Problem Properties 
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  clauses                                 3
% 1.53/0.97  conjectures                             0
% 1.53/0.97  EPR                                     0
% 1.53/0.97  Horn                                    2
% 1.53/0.97  unary                                   1
% 1.53/0.97  binary                                  2
% 1.53/0.97  lits                                    5
% 1.53/0.97  lits eq                                 1
% 1.53/0.97  fd_pure                                 0
% 1.53/0.97  fd_pseudo                               0
% 1.53/0.97  fd_cond                                 0
% 1.53/0.97  fd_pseudo_cond                          0
% 1.53/0.97  AC symbols                              0
% 1.53/0.97  
% 1.53/0.97  ------ Schedule dynamic 5 is on 
% 1.53/0.97  
% 1.53/0.97  ------ no conjectures: strip conj schedule 
% 1.53/0.97  
% 1.53/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  ------ 
% 1.53/0.97  Current options:
% 1.53/0.97  ------ 
% 1.53/0.97  
% 1.53/0.97  ------ Input Options
% 1.53/0.97  
% 1.53/0.97  --out_options                           all
% 1.53/0.97  --tptp_safe_out                         true
% 1.53/0.97  --problem_path                          ""
% 1.53/0.97  --include_path                          ""
% 1.53/0.97  --clausifier                            res/vclausify_rel
% 1.53/0.97  --clausifier_options                    --mode clausify
% 1.53/0.97  --stdin                                 false
% 1.53/0.97  --stats_out                             all
% 1.53/0.97  
% 1.53/0.97  ------ General Options
% 1.53/0.97  
% 1.53/0.97  --fof                                   false
% 1.53/0.97  --time_out_real                         305.
% 1.53/0.97  --time_out_virtual                      -1.
% 1.53/0.97  --symbol_type_check                     false
% 1.53/0.97  --clausify_out                          false
% 1.53/0.97  --sig_cnt_out                           false
% 1.53/0.97  --trig_cnt_out                          false
% 1.53/0.97  --trig_cnt_out_tolerance                1.
% 1.53/0.97  --trig_cnt_out_sk_spl                   false
% 1.53/0.97  --abstr_cl_out                          false
% 1.53/0.97  
% 1.53/0.97  ------ Global Options
% 1.53/0.97  
% 1.53/0.97  --schedule                              default
% 1.53/0.97  --add_important_lit                     false
% 1.53/0.97  --prop_solver_per_cl                    1000
% 1.53/0.97  --min_unsat_core                        false
% 1.53/0.97  --soft_assumptions                      false
% 1.53/0.97  --soft_lemma_size                       3
% 1.53/0.97  --prop_impl_unit_size                   0
% 1.53/0.97  --prop_impl_unit                        []
% 1.53/0.97  --share_sel_clauses                     true
% 1.53/0.97  --reset_solvers                         false
% 1.53/0.97  --bc_imp_inh                            [conj_cone]
% 1.53/0.97  --conj_cone_tolerance                   3.
% 1.53/0.97  --extra_neg_conj                        none
% 1.53/0.97  --large_theory_mode                     true
% 1.53/0.97  --prolific_symb_bound                   200
% 1.53/0.97  --lt_threshold                          2000
% 1.53/0.97  --clause_weak_htbl                      true
% 1.53/0.97  --gc_record_bc_elim                     false
% 1.53/0.97  
% 1.53/0.97  ------ Preprocessing Options
% 1.53/0.97  
% 1.53/0.97  --preprocessing_flag                    true
% 1.53/0.97  --time_out_prep_mult                    0.1
% 1.53/0.97  --splitting_mode                        input
% 1.53/0.97  --splitting_grd                         true
% 1.53/0.97  --splitting_cvd                         false
% 1.53/0.97  --splitting_cvd_svl                     false
% 1.53/0.97  --splitting_nvd                         32
% 1.53/0.97  --sub_typing                            true
% 1.53/0.97  --prep_gs_sim                           true
% 1.53/0.97  --prep_unflatten                        true
% 1.53/0.97  --prep_res_sim                          true
% 1.53/0.97  --prep_upred                            true
% 1.53/0.97  --prep_sem_filter                       exhaustive
% 1.53/0.97  --prep_sem_filter_out                   false
% 1.53/0.97  --pred_elim                             true
% 1.53/0.97  --res_sim_input                         true
% 1.53/0.97  --eq_ax_congr_red                       true
% 1.53/0.97  --pure_diseq_elim                       true
% 1.53/0.97  --brand_transform                       false
% 1.53/0.97  --non_eq_to_eq                          false
% 1.53/0.97  --prep_def_merge                        true
% 1.53/0.97  --prep_def_merge_prop_impl              false
% 1.53/0.97  --prep_def_merge_mbd                    true
% 1.53/0.97  --prep_def_merge_tr_red                 false
% 1.53/0.97  --prep_def_merge_tr_cl                  false
% 1.53/0.97  --smt_preprocessing                     true
% 1.53/0.97  --smt_ac_axioms                         fast
% 1.53/0.97  --preprocessed_out                      false
% 1.53/0.97  --preprocessed_stats                    false
% 1.53/0.97  
% 1.53/0.97  ------ Abstraction refinement Options
% 1.53/0.97  
% 1.53/0.97  --abstr_ref                             []
% 1.53/0.97  --abstr_ref_prep                        false
% 1.53/0.97  --abstr_ref_until_sat                   false
% 1.53/0.97  --abstr_ref_sig_restrict                funpre
% 1.53/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.53/0.97  --abstr_ref_under                       []
% 1.53/0.97  
% 1.53/0.97  ------ SAT Options
% 1.53/0.97  
% 1.53/0.97  --sat_mode                              false
% 1.53/0.97  --sat_fm_restart_options                ""
% 1.53/0.97  --sat_gr_def                            false
% 1.53/0.97  --sat_epr_types                         true
% 1.53/0.97  --sat_non_cyclic_types                  false
% 1.53/0.97  --sat_finite_models                     false
% 1.53/0.97  --sat_fm_lemmas                         false
% 1.53/0.97  --sat_fm_prep                           false
% 1.53/0.97  --sat_fm_uc_incr                        true
% 1.53/0.97  --sat_out_model                         small
% 1.53/0.97  --sat_out_clauses                       false
% 1.53/0.97  
% 1.53/0.97  ------ QBF Options
% 1.53/0.97  
% 1.53/0.97  --qbf_mode                              false
% 1.53/0.97  --qbf_elim_univ                         false
% 1.53/0.97  --qbf_dom_inst                          none
% 1.53/0.97  --qbf_dom_pre_inst                      false
% 1.53/0.97  --qbf_sk_in                             false
% 1.53/0.97  --qbf_pred_elim                         true
% 1.53/0.97  --qbf_split                             512
% 1.53/0.97  
% 1.53/0.97  ------ BMC1 Options
% 1.53/0.97  
% 1.53/0.97  --bmc1_incremental                      false
% 1.53/0.97  --bmc1_axioms                           reachable_all
% 1.53/0.97  --bmc1_min_bound                        0
% 1.53/0.97  --bmc1_max_bound                        -1
% 1.53/0.97  --bmc1_max_bound_default                -1
% 1.53/0.97  --bmc1_symbol_reachability              true
% 1.53/0.97  --bmc1_property_lemmas                  false
% 1.53/0.97  --bmc1_k_induction                      false
% 1.53/0.97  --bmc1_non_equiv_states                 false
% 1.53/0.97  --bmc1_deadlock                         false
% 1.53/0.97  --bmc1_ucm                              false
% 1.53/0.97  --bmc1_add_unsat_core                   none
% 1.53/0.97  --bmc1_unsat_core_children              false
% 1.53/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.53/0.97  --bmc1_out_stat                         full
% 1.53/0.97  --bmc1_ground_init                      false
% 1.53/0.97  --bmc1_pre_inst_next_state              false
% 1.53/0.97  --bmc1_pre_inst_state                   false
% 1.53/0.97  --bmc1_pre_inst_reach_state             false
% 1.53/0.97  --bmc1_out_unsat_core                   false
% 1.53/0.97  --bmc1_aig_witness_out                  false
% 1.53/0.97  --bmc1_verbose                          false
% 1.53/0.97  --bmc1_dump_clauses_tptp                false
% 1.53/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.53/0.97  --bmc1_dump_file                        -
% 1.53/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.53/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.53/0.97  --bmc1_ucm_extend_mode                  1
% 1.53/0.97  --bmc1_ucm_init_mode                    2
% 1.53/0.97  --bmc1_ucm_cone_mode                    none
% 1.53/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.53/0.97  --bmc1_ucm_relax_model                  4
% 1.53/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.53/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.53/0.97  --bmc1_ucm_layered_model                none
% 1.53/0.97  --bmc1_ucm_max_lemma_size               10
% 1.53/0.97  
% 1.53/0.97  ------ AIG Options
% 1.53/0.97  
% 1.53/0.97  --aig_mode                              false
% 1.53/0.97  
% 1.53/0.97  ------ Instantiation Options
% 1.53/0.97  
% 1.53/0.97  --instantiation_flag                    true
% 1.53/0.97  --inst_sos_flag                         false
% 1.53/0.97  --inst_sos_phase                        true
% 1.53/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.53/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.53/0.97  --inst_lit_sel_side                     none
% 1.53/0.97  --inst_solver_per_active                1400
% 1.53/0.97  --inst_solver_calls_frac                1.
% 1.53/0.97  --inst_passive_queue_type               priority_queues
% 1.53/0.97  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.53/0.97  --inst_passive_queues_freq              [25;2]
% 1.53/0.97  --inst_dismatching                      true
% 1.53/0.97  --inst_eager_unprocessed_to_passive     true
% 1.53/0.97  --inst_prop_sim_given                   true
% 1.53/0.97  --inst_prop_sim_new                     false
% 1.53/0.97  --inst_subs_new                         false
% 1.53/0.97  --inst_eq_res_simp                      false
% 1.53/0.97  --inst_subs_given                       false
% 1.53/0.97  --inst_orphan_elimination               true
% 1.53/0.97  --inst_learning_loop_flag               true
% 1.53/0.97  --inst_learning_start                   3000
% 1.53/0.97  --inst_learning_factor                  2
% 1.53/0.97  --inst_start_prop_sim_after_learn       3
% 1.53/0.97  --inst_sel_renew                        solver
% 1.53/0.97  --inst_lit_activity_flag                true
% 1.53/0.97  --inst_restr_to_given                   false
% 1.53/0.97  --inst_activity_threshold               500
% 1.53/0.97  --inst_out_proof                        true
% 1.53/0.97  
% 1.53/0.97  ------ Resolution Options
% 1.53/0.97  
% 1.53/0.97  --resolution_flag                       false
% 1.53/0.97  --res_lit_sel                           adaptive
% 1.53/0.97  --res_lit_sel_side                      none
% 1.53/0.97  --res_ordering                          kbo
% 1.53/0.97  --res_to_prop_solver                    active
% 1.53/0.97  --res_prop_simpl_new                    false
% 1.53/0.97  --res_prop_simpl_given                  true
% 1.53/0.97  --res_passive_queue_type                priority_queues
% 1.53/0.97  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.53/0.97  --res_passive_queues_freq               [15;5]
% 1.53/0.97  --res_forward_subs                      full
% 1.53/0.97  --res_backward_subs                     full
% 1.53/0.97  --res_forward_subs_resolution           true
% 1.53/0.97  --res_backward_subs_resolution          true
% 1.53/0.97  --res_orphan_elimination                true
% 1.53/0.97  --res_time_limit                        2.
% 1.53/0.97  --res_out_proof                         true
% 1.53/0.97  
% 1.53/0.97  ------ Superposition Options
% 1.53/0.97  
% 1.53/0.97  --superposition_flag                    true
% 1.53/0.97  --sup_passive_queue_type                priority_queues
% 1.53/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.53/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.53/0.97  --demod_completeness_check              fast
% 1.53/0.97  --demod_use_ground                      true
% 1.53/0.97  --sup_to_prop_solver                    passive
% 1.53/0.97  --sup_prop_simpl_new                    true
% 1.53/0.97  --sup_prop_simpl_given                  true
% 1.53/0.97  --sup_fun_splitting                     false
% 1.53/0.97  --sup_smt_interval                      50000
% 1.53/0.97  
% 1.53/0.97  ------ Superposition Simplification Setup
% 1.53/0.97  
% 1.53/0.97  --sup_indices_passive                   []
% 1.53/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.53/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.53/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.97  --sup_full_bw                           [BwDemod]
% 1.53/0.97  --sup_immed_triv                        [TrivRules]
% 1.53/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.53/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.97  --sup_immed_bw_main                     []
% 1.53/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.53/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.53/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.53/0.97  
% 1.53/0.97  ------ Combination Options
% 1.53/0.97  
% 1.53/0.97  --comb_res_mult                         3
% 1.53/0.97  --comb_sup_mult                         2
% 1.53/0.97  --comb_inst_mult                        10
% 1.53/0.97  
% 1.53/0.97  ------ Debug Options
% 1.53/0.97  
% 1.53/0.97  --dbg_backtrace                         false
% 1.53/0.97  --dbg_dump_prop_clauses                 false
% 1.53/0.97  --dbg_dump_prop_clauses_file            -
% 1.53/0.97  --dbg_out_stat                          false
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  ------ Proving...
% 1.53/0.97  
% 1.53/0.97  
% 1.53/0.97  % SZS status Theorem for theBenchmark.p
% 1.53/0.97  
% 1.53/0.97   Resolution empty clause
% 1.53/0.97  
% 1.53/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.53/0.97  
% 1.53/0.97  fof(f10,conjecture,(
% 1.53/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f11,negated_conjecture,(
% 1.53/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 1.53/0.97    inference(negated_conjecture,[],[f10])).
% 1.53/0.97  
% 1.53/0.97  fof(f30,plain,(
% 1.53/0.97    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f11])).
% 1.53/0.97  
% 1.53/0.97  fof(f31,plain,(
% 1.53/0.97    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f30])).
% 1.53/0.97  
% 1.53/0.97  fof(f33,plain,(
% 1.53/0.97    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.97    inference(nnf_transformation,[],[f31])).
% 1.53/0.97  
% 1.53/0.97  fof(f34,plain,(
% 1.53/0.97    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f33])).
% 1.53/0.97  
% 1.53/0.97  fof(f37,plain,(
% 1.53/0.97    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & (r1_waybel_7(X0,X1,sK2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.53/0.97    introduced(choice_axiom,[])).
% 1.53/0.97  
% 1.53/0.97  fof(f36,plain,(
% 1.53/0.97    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & (r1_waybel_7(X0,sK1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK1))) )),
% 1.53/0.97    introduced(choice_axiom,[])).
% 1.53/0.97  
% 1.53/0.97  fof(f35,plain,(
% 1.53/0.97    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.53/0.97    introduced(choice_axiom,[])).
% 1.53/0.97  
% 1.53/0.97  fof(f38,plain,(
% 1.53/0.97    (((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.53/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f37,f36,f35])).
% 1.53/0.97  
% 1.53/0.97  fof(f57,plain,(
% 1.53/0.97    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.53/0.97    inference(cnf_transformation,[],[f38])).
% 1.53/0.97  
% 1.53/0.97  fof(f4,axiom,(
% 1.53/0.97    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f42,plain,(
% 1.53/0.97    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.53/0.97    inference(cnf_transformation,[],[f4])).
% 1.53/0.97  
% 1.53/0.97  fof(f72,plain,(
% 1.53/0.97    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.53/0.97    inference(definition_unfolding,[],[f57,f42])).
% 1.53/0.97  
% 1.53/0.97  fof(f58,plain,(
% 1.53/0.97    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 1.53/0.97    inference(cnf_transformation,[],[f38])).
% 1.53/0.97  
% 1.53/0.97  fof(f71,plain,(
% 1.53/0.97    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.53/0.97    inference(definition_unfolding,[],[f58,f42])).
% 1.53/0.97  
% 1.53/0.97  fof(f7,axiom,(
% 1.53/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f14,plain,(
% 1.53/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.53/0.97    inference(pure_predicate_removal,[],[f7])).
% 1.53/0.97  
% 1.53/0.97  fof(f24,plain,(
% 1.53/0.97    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f14])).
% 1.53/0.97  
% 1.53/0.97  fof(f25,plain,(
% 1.53/0.97    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f24])).
% 1.53/0.97  
% 1.53/0.97  fof(f48,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f25])).
% 1.53/0.97  
% 1.53/0.97  fof(f67,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(definition_unfolding,[],[f48,f42,f42,f42,f42])).
% 1.53/0.97  
% 1.53/0.97  fof(f56,plain,(
% 1.53/0.97    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 1.53/0.97    inference(cnf_transformation,[],[f38])).
% 1.53/0.97  
% 1.53/0.97  fof(f73,plain,(
% 1.53/0.97    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 1.53/0.97    inference(definition_unfolding,[],[f56,f42])).
% 1.53/0.97  
% 1.53/0.97  fof(f55,plain,(
% 1.53/0.97    ~v1_xboole_0(sK1)),
% 1.53/0.97    inference(cnf_transformation,[],[f38])).
% 1.53/0.97  
% 1.53/0.97  fof(f2,axiom,(
% 1.53/0.97    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f17,plain,(
% 1.53/0.97    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.53/0.97    inference(ennf_transformation,[],[f2])).
% 1.53/0.97  
% 1.53/0.97  fof(f40,plain,(
% 1.53/0.97    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f17])).
% 1.53/0.97  
% 1.53/0.97  fof(f54,plain,(
% 1.53/0.97    l1_pre_topc(sK0)),
% 1.53/0.97    inference(cnf_transformation,[],[f38])).
% 1.53/0.97  
% 1.53/0.97  fof(f52,plain,(
% 1.53/0.97    ~v2_struct_0(sK0)),
% 1.53/0.97    inference(cnf_transformation,[],[f38])).
% 1.53/0.97  
% 1.53/0.97  fof(f3,axiom,(
% 1.53/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f18,plain,(
% 1.53/0.97    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f3])).
% 1.53/0.97  
% 1.53/0.97  fof(f19,plain,(
% 1.53/0.97    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f18])).
% 1.53/0.97  
% 1.53/0.97  fof(f41,plain,(
% 1.53/0.97    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f19])).
% 1.53/0.97  
% 1.53/0.97  fof(f59,plain,(
% 1.53/0.97    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.53/0.97    inference(cnf_transformation,[],[f38])).
% 1.53/0.97  
% 1.53/0.97  fof(f70,plain,(
% 1.53/0.97    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.53/0.97    inference(definition_unfolding,[],[f59,f42])).
% 1.53/0.97  
% 1.53/0.97  fof(f1,axiom,(
% 1.53/0.97    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f16,plain,(
% 1.53/0.97    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.53/0.97    inference(ennf_transformation,[],[f1])).
% 1.53/0.97  
% 1.53/0.97  fof(f39,plain,(
% 1.53/0.97    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f16])).
% 1.53/0.97  
% 1.53/0.97  fof(f5,axiom,(
% 1.53/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f15,plain,(
% 1.53/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.53/0.97    inference(pure_predicate_removal,[],[f5])).
% 1.53/0.97  
% 1.53/0.97  fof(f20,plain,(
% 1.53/0.97    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f15])).
% 1.53/0.97  
% 1.53/0.97  fof(f21,plain,(
% 1.53/0.97    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f20])).
% 1.53/0.97  
% 1.53/0.97  fof(f44,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f21])).
% 1.53/0.97  
% 1.53/0.97  fof(f63,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(definition_unfolding,[],[f44,f42,f42,f42])).
% 1.53/0.97  
% 1.53/0.97  fof(f62,plain,(
% 1.53/0.97    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.53/0.97    inference(cnf_transformation,[],[f38])).
% 1.53/0.97  
% 1.53/0.97  fof(f8,axiom,(
% 1.53/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f26,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f8])).
% 1.53/0.97  
% 1.53/0.97  fof(f27,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f26])).
% 1.53/0.97  
% 1.53/0.97  fof(f32,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(nnf_transformation,[],[f27])).
% 1.53/0.97  
% 1.53/0.97  fof(f50,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f32])).
% 1.53/0.97  
% 1.53/0.97  fof(f53,plain,(
% 1.53/0.97    v2_pre_topc(sK0)),
% 1.53/0.97    inference(cnf_transformation,[],[f38])).
% 1.53/0.97  
% 1.53/0.97  fof(f60,plain,(
% 1.53/0.97    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.53/0.97    inference(cnf_transformation,[],[f38])).
% 1.53/0.97  
% 1.53/0.97  fof(f43,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f21])).
% 1.53/0.97  
% 1.53/0.97  fof(f64,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(definition_unfolding,[],[f43,f42,f42,f42])).
% 1.53/0.97  
% 1.53/0.97  fof(f6,axiom,(
% 1.53/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f12,plain,(
% 1.53/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.53/0.97    inference(pure_predicate_removal,[],[f6])).
% 1.53/0.97  
% 1.53/0.97  fof(f13,plain,(
% 1.53/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 1.53/0.97    inference(pure_predicate_removal,[],[f12])).
% 1.53/0.97  
% 1.53/0.97  fof(f22,plain,(
% 1.53/0.97    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f13])).
% 1.53/0.97  
% 1.53/0.97  fof(f23,plain,(
% 1.53/0.97    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f22])).
% 1.53/0.97  
% 1.53/0.97  fof(f46,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f23])).
% 1.53/0.97  
% 1.53/0.97  fof(f65,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(definition_unfolding,[],[f46,f42,f42,f42])).
% 1.53/0.97  
% 1.53/0.97  fof(f9,axiom,(
% 1.53/0.97    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 1.53/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.53/0.97  
% 1.53/0.97  fof(f28,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.53/0.97    inference(ennf_transformation,[],[f9])).
% 1.53/0.97  
% 1.53/0.97  fof(f29,plain,(
% 1.53/0.97    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.53/0.97    inference(flattening,[],[f28])).
% 1.53/0.97  
% 1.53/0.97  fof(f51,plain,(
% 1.53/0.97    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f29])).
% 1.53/0.97  
% 1.53/0.97  fof(f69,plain,(
% 1.53/0.97    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(definition_unfolding,[],[f51,f42,f42,f42,f42])).
% 1.53/0.97  
% 1.53/0.97  fof(f61,plain,(
% 1.53/0.97    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 1.53/0.97    inference(cnf_transformation,[],[f38])).
% 1.53/0.97  
% 1.53/0.97  fof(f49,plain,(
% 1.53/0.97    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.53/0.97    inference(cnf_transformation,[],[f32])).
% 1.53/0.97  
% 1.53/0.97  cnf(c_17,negated_conjecture,
% 1.53/0.97      ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.53/0.97      inference(cnf_transformation,[],[f72]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_16,negated_conjecture,
% 1.53/0.97      ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.53/0.97      inference(cnf_transformation,[],[f71]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_7,plain,
% 1.53/0.97      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 1.53/0.97      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.97      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.97      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.53/0.97      | v2_struct_0(X2)
% 1.53/0.97      | v1_xboole_0(X1)
% 1.53/0.97      | v1_xboole_0(X0)
% 1.53/0.97      | ~ l1_struct_0(X2) ),
% 1.53/0.97      inference(cnf_transformation,[],[f67]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_18,negated_conjecture,
% 1.53/0.97      ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
% 1.53/0.97      inference(cnf_transformation,[],[f73]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_306,plain,
% 1.53/0.97      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.97      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.97      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 1.53/0.97      | v2_struct_0(X2)
% 1.53/0.97      | v1_xboole_0(X1)
% 1.53/0.97      | v1_xboole_0(X0)
% 1.53/0.97      | ~ l1_struct_0(X2)
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 1.53/0.97      | sK1 != X0 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_307,plain,
% 1.53/0.97      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.97      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | v1_xboole_0(X0)
% 1.53/0.97      | v1_xboole_0(sK1)
% 1.53/0.97      | ~ l1_struct_0(X1)
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_306]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_19,negated_conjecture,
% 1.53/0.97      ( ~ v1_xboole_0(sK1) ),
% 1.53/0.97      inference(cnf_transformation,[],[f55]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_311,plain,
% 1.53/0.97      ( v1_xboole_0(X0)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.53/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ l1_struct_0(X1)
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.53/0.97      inference(global_propositional_subsumption,[status(thm)],[c_307,c_19]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_312,plain,
% 1.53/0.97      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.97      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | v1_xboole_0(X0)
% 1.53/0.97      | ~ l1_struct_0(X1)
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.53/0.97      inference(renaming,[status(thm)],[c_311]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1,plain,
% 1.53/0.97      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f40]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_20,negated_conjecture,
% 1.53/0.97      ( l1_pre_topc(sK0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f54]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_478,plain,
% 1.53/0.97      ( l1_struct_0(X0) | sK0 != X0 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_479,plain,
% 1.53/0.97      ( l1_struct_0(sK0) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_478]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1040,plain,
% 1.53/0.97      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.53/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.97      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | v1_xboole_0(X0)
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | sK0 != X1 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_312,c_479]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1041,plain,
% 1.53/0.97      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.97      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.53/0.97      | v2_struct_0(sK0)
% 1.53/0.97      | v1_xboole_0(X0)
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_1040]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_22,negated_conjecture,
% 1.53/0.97      ( ~ v2_struct_0(sK0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f52]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1045,plain,
% 1.53/0.97      ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.53/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | v1_xboole_0(X0)
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.53/0.97      inference(global_propositional_subsumption,[status(thm)],[c_1041,c_22]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1046,plain,
% 1.53/0.97      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.97      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.53/0.97      | v1_xboole_0(X0)
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 1.53/0.97      inference(renaming,[status(thm)],[c_1045]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1489,plain,
% 1.53/0.97      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.97      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.53/0.97      | v1_xboole_0(X0)
% 1.53/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | sK1 != sK1 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_1046]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_1767,plain,
% 1.53/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.97      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.53/0.97      | v1_xboole_0(X0)
% 1.53/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | sK1 != sK1 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_17,c_1489]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2,plain,
% 1.53/0.97      ( v2_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | ~ l1_struct_0(X0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f41]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_956,plain,
% 1.53/0.97      ( v2_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK0 != X0 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_2,c_479]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_957,plain,
% 1.53/0.97      ( v2_struct_0(sK0) | ~ v1_xboole_0(k2_struct_0(sK0)) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_956]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_60,plain,
% 1.53/0.97      ( v2_struct_0(sK0)
% 1.53/0.97      | ~ v1_xboole_0(k2_struct_0(sK0))
% 1.53/0.97      | ~ l1_struct_0(sK0) ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_63,plain,
% 1.53/0.97      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_1]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_959,plain,
% 1.53/0.97      ( ~ v1_xboole_0(k2_struct_0(sK0)) ),
% 1.53/0.97      inference(global_propositional_subsumption,
% 1.53/0.97                [status(thm)],
% 1.53/0.97                [c_957,c_22,c_20,c_60,c_63]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2508,plain,
% 1.53/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.97      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 1.53/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 1.53/0.97      | k2_struct_0(sK0) != X0
% 1.53/0.97      | sK1 != sK1 ),
% 1.53/0.97      inference(resolution_lifted,[status(thm)],[c_1767,c_959]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2509,plain,
% 1.53/0.97      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.53/0.97      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.53/0.97      inference(unflattening,[status(thm)],[c_2508]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_15,negated_conjecture,
% 1.53/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
% 1.53/0.97      inference(cnf_transformation,[],[f70]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_0,plain,
% 1.53/0.97      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 1.53/0.97      | ~ l1_struct_0(X0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f39]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_66,plain,
% 1.53/0.97      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.97      | ~ l1_struct_0(sK0) ),
% 1.53/0.97      inference(instantiation,[status(thm)],[c_0]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_2511,plain,
% 1.53/0.97      ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.97      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 1.53/0.97      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.53/0.97      inference(global_propositional_subsumption,
% 1.53/0.97                [status(thm)],
% 1.53/0.97                [c_2509,c_20,c_15,c_63,c_66]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_3106,plain,
% 1.53/0.97      ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.53/0.97      inference(equality_resolution_simp,[status(thm)],[c_2511]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_3,plain,
% 1.53/0.97      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.97      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.97      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 1.53/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.53/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.97      | v2_struct_0(X2)
% 1.53/0.97      | v1_xboole_0(X1)
% 1.53/0.97      | v1_xboole_0(X0)
% 1.53/0.97      | ~ l1_struct_0(X2) ),
% 1.53/0.97      inference(cnf_transformation,[],[f63]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_12,negated_conjecture,
% 1.53/0.97      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.97      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.53/0.97      inference(cnf_transformation,[],[f62]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_166,plain,
% 1.53/0.97      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.97      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.53/0.97      inference(prop_impl,[status(thm)],[c_12]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_9,plain,
% 1.53/0.97      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.53/0.97      | r3_waybel_9(X0,X1,X2)
% 1.53/0.97      | ~ l1_waybel_0(X1,X0)
% 1.53/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.53/0.97      | ~ v2_pre_topc(X0)
% 1.53/0.97      | ~ v7_waybel_0(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | v2_struct_0(X0)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.97      | ~ l1_pre_topc(X0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f50]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_21,negated_conjecture,
% 1.53/0.97      ( v2_pre_topc(sK0) ),
% 1.53/0.97      inference(cnf_transformation,[],[f53]) ).
% 1.53/0.97  
% 1.53/0.97  cnf(c_429,plain,
% 1.53/0.97      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.53/0.97      | r3_waybel_9(X0,X1,X2)
% 1.53/0.97      | ~ l1_waybel_0(X1,X0)
% 1.53/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.53/0.97      | ~ v7_waybel_0(X1)
% 1.53/0.97      | ~ v4_orders_2(X1)
% 1.53/0.97      | v2_struct_0(X0)
% 1.53/0.97      | v2_struct_0(X1)
% 1.53/0.98      | ~ l1_pre_topc(X0)
% 1.53/0.98      | sK0 != X0 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_430,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.53/0.98      | r3_waybel_9(sK0,X0,X1)
% 1.53/0.98      | ~ l1_waybel_0(X0,sK0)
% 1.53/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.53/0.98      | ~ v7_waybel_0(X0)
% 1.53/0.98      | ~ v4_orders_2(X0)
% 1.53/0.98      | v2_struct_0(X0)
% 1.53/0.98      | v2_struct_0(sK0)
% 1.53/0.98      | ~ l1_pre_topc(sK0) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_429]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_434,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.53/0.98      | r3_waybel_9(sK0,X0,X1)
% 1.53/0.98      | ~ l1_waybel_0(X0,sK0)
% 1.53/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.53/0.98      | ~ v7_waybel_0(X0)
% 1.53/0.98      | ~ v4_orders_2(X0)
% 1.53/0.98      | v2_struct_0(X0) ),
% 1.53/0.98      inference(global_propositional_subsumption,
% 1.53/0.98                [status(thm)],
% 1.53/0.98                [c_430,c_22,c_20]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_807,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ l1_waybel_0(X0,sK0)
% 1.53/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.53/0.98      | ~ v7_waybel_0(X0)
% 1.53/0.98      | ~ v4_orders_2(X0)
% 1.53/0.98      | v2_struct_0(X0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 1.53/0.98      | sK2 != X1
% 1.53/0.98      | sK0 != sK0 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_166,c_434]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_808,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.53/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_807]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_14,negated_conjecture,
% 1.53/0.98      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 1.53/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_810,plain,
% 1.53/0.98      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.53/0.98      inference(global_propositional_subsumption,[status(thm)],[c_808,c_14]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_811,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_810]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_847,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(X2)
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | ~ l1_struct_0(X2)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 1.53/0.98      | sK0 != X2 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_811]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_848,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(sK0)
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | ~ l1_struct_0(sK0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_847]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_852,plain,
% 1.53/0.98      ( v1_xboole_0(X0)
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.53/0.98      inference(global_propositional_subsumption,
% 1.53/0.98                [status(thm)],
% 1.53/0.98                [c_848,c_22,c_20,c_63]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_853,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_852]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1444,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.53/0.98      | sK1 != X0 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_853,c_16]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1445,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | v1_xboole_0(sK1)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_1444]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1449,plain,
% 1.53/0.98      ( v1_xboole_0(X0)
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1445,c_19]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1450,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_1449]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1793,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.53/0.98      | sK1 != sK1 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_1450]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2485,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.53/0.98      | k2_struct_0(sK0) != X0
% 1.53/0.98      | sK1 != sK1 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_1793,c_959]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2486,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_2485]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_4,plain,
% 1.53/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | v2_struct_0(X2)
% 1.53/0.98      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | ~ l1_struct_0(X2) ),
% 1.53/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1007,plain,
% 1.53/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | v2_struct_0(X2)
% 1.53/0.98      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | sK0 != X2 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_479]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1008,plain,
% 1.53/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.53/0.98      | v2_struct_0(sK0)
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_1007]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1012,plain,
% 1.53/0.98      ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0) ),
% 1.53/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1008,c_22]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1013,plain,
% 1.53/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_1012]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1339,plain,
% 1.53/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.53/0.98      | sK1 != X0 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_1013,c_16]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1340,plain,
% 1.53/0.98      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | v1_xboole_0(sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_1339]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1344,plain,
% 1.53/0.98      ( v1_xboole_0(X0)
% 1.53/0.98      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1340,c_19]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1345,plain,
% 1.53/0.98      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_1344]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1892,plain,
% 1.53/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.53/0.98      | sK1 != sK1 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_1345]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2434,plain,
% 1.53/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.53/0.98      | k2_struct_0(sK0) != X0
% 1.53/0.98      | sK1 != sK1 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_1892,c_959]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2435,plain,
% 1.53/0.98      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.53/0.98      | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_2434]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2437,plain,
% 1.53/0.98      ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.53/0.98      inference(global_propositional_subsumption,
% 1.53/0.98                [status(thm)],
% 1.53/0.98                [c_2435,c_20,c_15,c_63,c_66]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_5,plain,
% 1.53/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.53/0.98      | v2_struct_0(X2)
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | ~ l1_struct_0(X2) ),
% 1.53/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_974,plain,
% 1.53/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 1.53/0.98      | v2_struct_0(X2)
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | sK0 != X2 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_479]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_975,plain,
% 1.53/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.53/0.98      | v2_struct_0(sK0)
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_974]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_979,plain,
% 1.53/0.98      ( v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0) ),
% 1.53/0.98      inference(global_propositional_subsumption,[status(thm)],[c_975,c_22]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_980,plain,
% 1.53/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_979]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1369,plain,
% 1.53/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.53/0.98      | sK1 != X0 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_980,c_16]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1370,plain,
% 1.53/0.98      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | v1_xboole_0(sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_1369]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1374,plain,
% 1.53/0.98      ( v1_xboole_0(X0)
% 1.53/0.98      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1370,c_19]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1375,plain,
% 1.53/0.98      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_1374]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1869,plain,
% 1.53/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.53/0.98      | sK1 != sK1 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_1375]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2448,plain,
% 1.53/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.53/0.98      | k2_struct_0(sK0) != X0
% 1.53/0.98      | sK1 != sK1 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_1869,c_959]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2449,plain,
% 1.53/0.98      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.53/0.98      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_2448]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2451,plain,
% 1.53/0.98      ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.53/0.98      inference(global_propositional_subsumption,
% 1.53/0.98                [status(thm)],
% 1.53/0.98                [c_2449,c_20,c_15,c_63,c_66]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2488,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.53/0.98      inference(global_propositional_subsumption,
% 1.53/0.98                [status(thm)],
% 1.53/0.98                [c_2486,c_20,c_15,c_63,c_66,c_2437,c_2451]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3108,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.53/0.98      inference(equality_resolution_simp,[status(thm)],[c_2488]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3197,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
% 1.53/0.98      inference(prop_impl,[status(thm)],[c_3111]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3198,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_3197]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3223,plain,
% 1.53/0.98      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ r1_waybel_7(sK0,sK1,sK2) ),
% 1.53/0.98      inference(subtyping,[status(esa)],[c_3198]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3327,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2) != iProver_top ),
% 1.53/0.98      inference(predicate_to_equality,[status(thm)],[c_3223]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_11,plain,
% 1.53/0.98      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.53/0.98      | v2_struct_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | ~ l1_struct_0(X1)
% 1.53/0.98      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 1.53/0.98      inference(cnf_transformation,[],[f69]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_345,plain,
% 1.53/0.98      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 1.53/0.98      | v2_struct_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | ~ l1_struct_0(X1)
% 1.53/0.98      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 1.53/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.53/0.98      | sK1 != X0 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_346,plain,
% 1.53/0.98      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.53/0.98      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.53/0.98      | v2_struct_0(X0)
% 1.53/0.98      | v1_xboole_0(sK1)
% 1.53/0.98      | ~ l1_struct_0(X0)
% 1.53/0.98      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.53/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_345]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_350,plain,
% 1.53/0.98      ( v2_struct_0(X0)
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.53/0.98      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.53/0.98      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.53/0.98      | ~ l1_struct_0(X0)
% 1.53/0.98      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.53/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.53/0.98      inference(global_propositional_subsumption,[status(thm)],[c_346,c_19]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_351,plain,
% 1.53/0.98      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.53/0.98      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.53/0.98      | v2_struct_0(X0)
% 1.53/0.98      | ~ l1_struct_0(X0)
% 1.53/0.98      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.53/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_350]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_945,plain,
% 1.53/0.98      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.53/0.98      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 1.53/0.98      | v2_struct_0(X0)
% 1.53/0.98      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 1.53/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.53/0.98      | sK0 != X0 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_351,c_479]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_946,plain,
% 1.53/0.98      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.53/0.98      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.53/0.98      | v2_struct_0(sK0)
% 1.53/0.98      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.53/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_945]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_948,plain,
% 1.53/0.98      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 1.53/0.98      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 1.53/0.98      inference(global_propositional_subsumption,
% 1.53/0.98                [status(thm)],
% 1.53/0.98                [c_946,c_22,c_17,c_16,c_15]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3122,plain,
% 1.53/0.98      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.53/0.98      inference(equality_resolution_simp,[status(thm)],[c_948]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3221,plain,
% 1.53/0.98      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 1.53/0.98      inference(subtyping,[status(esa)],[c_3122]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3334,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,sK1,sK2) != iProver_top ),
% 1.53/0.98      inference(light_normalisation,[status(thm)],[c_3327,c_3221]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_13,negated_conjecture,
% 1.53/0.98      ( r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.53/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_168,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 1.53/0.98      inference(prop_impl,[status(thm)],[c_13]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_10,plain,
% 1.53/0.98      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.53/0.98      | ~ r3_waybel_9(X0,X1,X2)
% 1.53/0.98      | ~ l1_waybel_0(X1,X0)
% 1.53/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.53/0.98      | ~ v2_pre_topc(X0)
% 1.53/0.98      | ~ v7_waybel_0(X1)
% 1.53/0.98      | ~ v4_orders_2(X1)
% 1.53/0.98      | v2_struct_0(X0)
% 1.53/0.98      | v2_struct_0(X1)
% 1.53/0.98      | ~ l1_pre_topc(X0) ),
% 1.53/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_396,plain,
% 1.53/0.98      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 1.53/0.98      | ~ r3_waybel_9(X0,X1,X2)
% 1.53/0.98      | ~ l1_waybel_0(X1,X0)
% 1.53/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.53/0.98      | ~ v7_waybel_0(X1)
% 1.53/0.98      | ~ v4_orders_2(X1)
% 1.53/0.98      | v2_struct_0(X0)
% 1.53/0.98      | v2_struct_0(X1)
% 1.53/0.98      | ~ l1_pre_topc(X0)
% 1.53/0.98      | sK0 != X0 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_397,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.53/0.98      | ~ r3_waybel_9(sK0,X0,X1)
% 1.53/0.98      | ~ l1_waybel_0(X0,sK0)
% 1.53/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.53/0.98      | ~ v7_waybel_0(X0)
% 1.53/0.98      | ~ v4_orders_2(X0)
% 1.53/0.98      | v2_struct_0(X0)
% 1.53/0.98      | v2_struct_0(sK0)
% 1.53/0.98      | ~ l1_pre_topc(sK0) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_396]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_401,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.53/0.98      | ~ r3_waybel_9(sK0,X0,X1)
% 1.53/0.98      | ~ l1_waybel_0(X0,sK0)
% 1.53/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.53/0.98      | ~ v7_waybel_0(X0)
% 1.53/0.98      | ~ v4_orders_2(X0)
% 1.53/0.98      | v2_struct_0(X0) ),
% 1.53/0.98      inference(global_propositional_subsumption,
% 1.53/0.98                [status(thm)],
% 1.53/0.98                [c_397,c_22,c_20]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_781,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ l1_waybel_0(X0,sK0)
% 1.53/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.53/0.98      | ~ v7_waybel_0(X0)
% 1.53/0.98      | ~ v4_orders_2(X0)
% 1.53/0.98      | v2_struct_0(X0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 1.53/0.98      | sK2 != X1
% 1.53/0.98      | sK0 != sK0 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_168,c_401]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_782,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.53/0.98      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_781]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_784,plain,
% 1.53/0.98      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.53/0.98      inference(global_propositional_subsumption,[status(thm)],[c_782,c_14]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_785,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_784]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_895,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(X2)
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | ~ l1_struct_0(X2)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 1.53/0.98      | sK0 != X2 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_785]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_896,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(sK0)
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | ~ l1_struct_0(sK0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_895]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_900,plain,
% 1.53/0.98      ( v1_xboole_0(X0)
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.53/0.98      inference(global_propositional_subsumption,
% 1.53/0.98                [status(thm)],
% 1.53/0.98                [c_896,c_22,c_20,c_63]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_901,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_900]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1399,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 1.53/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X1)
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 1.53/0.98      | sK1 != X0 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_901,c_16]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1400,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | v1_xboole_0(sK1)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_1399]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1404,plain,
% 1.53/0.98      ( v1_xboole_0(X0)
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1400,c_19]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1405,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_1404]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_1831,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v1_xboole_0(X0)
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.53/0.98      | sK1 != sK1 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_1405]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2462,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 1.53/0.98      | k2_struct_0(sK0) != X0
% 1.53/0.98      | sK1 != sK1 ),
% 1.53/0.98      inference(resolution_lifted,[status(thm)],[c_1831,c_959]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2463,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 1.53/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.53/0.98      inference(unflattening,[status(thm)],[c_2462]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_2465,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 1.53/0.98      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,k2_struct_0(sK0),sK1)
% 1.53/0.98      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0))) ),
% 1.53/0.98      inference(global_propositional_subsumption,
% 1.53/0.98                [status(thm)],
% 1.53/0.98                [c_2463,c_20,c_15,c_63,c_66,c_2437,c_2451]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3114,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 1.53/0.98      inference(equality_resolution_simp,[status(thm)],[c_2465]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3199,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,sK1,sK2)
% 1.53/0.98      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
% 1.53/0.98      inference(prop_impl,[status(thm)],[c_3117]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3200,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2) ),
% 1.53/0.98      inference(renaming,[status(thm)],[c_3199]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3222,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2) ),
% 1.53/0.98      inference(subtyping,[status(esa)],[c_3200]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3328,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
% 1.53/0.98      | r1_waybel_7(sK0,sK1,sK2) = iProver_top ),
% 1.53/0.98      inference(predicate_to_equality,[status(thm)],[c_3222]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3331,plain,
% 1.53/0.98      ( r1_waybel_7(sK0,sK1,sK2) = iProver_top ),
% 1.53/0.98      inference(light_normalisation,[status(thm)],[c_3328,c_3221]) ).
% 1.53/0.98  
% 1.53/0.98  cnf(c_3336,plain,
% 1.53/0.98      ( $false ),
% 1.53/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_3334,c_3331]) ).
% 1.53/0.98  
% 1.53/0.98  
% 1.53/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.53/0.98  
% 1.53/0.98  ------                               Statistics
% 1.53/0.98  
% 1.53/0.98  ------ General
% 1.53/0.98  
% 1.53/0.98  abstr_ref_over_cycles:                  0
% 1.53/0.98  abstr_ref_under_cycles:                 0
% 1.53/0.98  gc_basic_clause_elim:                   0
% 1.53/0.98  forced_gc_time:                         0
% 1.53/0.98  parsing_time:                           0.015
% 1.53/0.98  unif_index_cands_time:                  0.
% 1.53/0.98  unif_index_add_time:                    0.
% 1.53/0.98  orderings_time:                         0.
% 1.53/0.98  out_proof_time:                         0.014
% 1.53/0.98  total_time:                             0.149
% 1.53/0.98  num_of_symbols:                         57
% 1.53/0.98  num_of_terms:                           1310
% 1.53/0.98  
% 1.53/0.98  ------ Preprocessing
% 1.53/0.98  
% 1.53/0.98  num_of_splits:                          0
% 1.53/0.98  num_of_split_atoms:                     0
% 1.53/0.98  num_of_reused_defs:                     0
% 1.53/0.98  num_eq_ax_congr_red:                    9
% 1.53/0.98  num_of_sem_filtered_clauses:            6
% 1.53/0.98  num_of_subtypes:                        5
% 1.53/0.98  monotx_restored_types:                  0
% 1.53/0.98  sat_num_of_epr_types:                   0
% 1.53/0.98  sat_num_of_non_cyclic_types:            0
% 1.53/0.98  sat_guarded_non_collapsed_types:        0
% 1.53/0.98  num_pure_diseq_elim:                    0
% 1.53/0.98  simp_replaced_by:                       0
% 1.53/0.98  res_preprocessed:                       51
% 1.53/0.98  prep_upred:                             0
% 1.53/0.98  prep_unflattend:                        39
% 1.53/0.98  smt_new_axioms:                         0
% 1.53/0.98  pred_elim_cands:                        1
% 1.53/0.98  pred_elim:                              11
% 1.53/0.98  pred_elim_cl:                           11
% 1.53/0.98  pred_elim_cycles:                       25
% 1.53/0.98  merged_defs:                            10
% 1.53/0.98  merged_defs_ncl:                        0
% 1.53/0.98  bin_hyper_res:                          12
% 1.53/0.98  prep_cycles:                            5
% 1.53/0.98  pred_elim_time:                         0.088
% 1.53/0.98  splitting_time:                         0.
% 1.53/0.98  sem_filter_time:                        0.
% 1.53/0.98  monotx_time:                            0.
% 1.53/0.98  subtype_inf_time:                       0.
% 1.53/0.98  
% 1.53/0.98  ------ Problem properties
% 1.53/0.98  
% 1.53/0.98  clauses:                                3
% 1.53/0.98  conjectures:                            0
% 1.53/0.98  epr:                                    0
% 1.53/0.98  horn:                                   2
% 1.53/0.98  ground:                                 3
% 1.53/0.98  unary:                                  1
% 1.53/0.98  binary:                                 2
% 1.53/0.98  lits:                                   5
% 1.53/0.98  lits_eq:                                1
% 1.53/0.98  fd_pure:                                0
% 1.53/0.98  fd_pseudo:                              0
% 1.53/0.98  fd_cond:                                0
% 1.53/0.98  fd_pseudo_cond:                         0
% 1.53/0.98  ac_symbols:                             0
% 1.53/0.98  
% 1.53/0.98  ------ Propositional Solver
% 1.53/0.98  
% 1.53/0.98  prop_solver_calls:                      25
% 1.53/0.98  prop_fast_solver_calls:                 1258
% 1.53/0.98  smt_solver_calls:                       0
% 1.53/0.98  smt_fast_solver_calls:                  0
% 1.53/0.98  prop_num_of_clauses:                    404
% 1.53/0.98  prop_preprocess_simplified:             1320
% 1.53/0.98  prop_fo_subsumed:                       51
% 1.53/0.98  prop_solver_time:                       0.
% 1.53/0.98  smt_solver_time:                        0.
% 1.53/0.98  smt_fast_solver_time:                   0.
% 1.53/0.98  prop_fast_solver_time:                  0.
% 1.53/0.98  prop_unsat_core_time:                   0.
% 1.53/0.98  
% 1.53/0.98  ------ QBF
% 1.53/0.98  
% 1.53/0.98  qbf_q_res:                              0
% 1.53/0.98  qbf_num_tautologies:                    0
% 1.53/0.98  qbf_prep_cycles:                        0
% 1.53/0.98  
% 1.53/0.98  ------ BMC1
% 1.53/0.98  
% 1.53/0.98  bmc1_current_bound:                     -1
% 1.53/0.98  bmc1_last_solved_bound:                 -1
% 1.53/0.98  bmc1_unsat_core_size:                   -1
% 1.53/0.98  bmc1_unsat_core_parents_size:           -1
% 1.53/0.98  bmc1_merge_next_fun:                    0
% 1.53/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.53/0.98  
% 1.53/0.98  ------ Instantiation
% 1.53/0.98  
% 1.53/0.98  inst_num_of_clauses:                    9
% 1.53/0.98  inst_num_in_passive:                    0
% 1.53/0.98  inst_num_in_active:                     0
% 1.53/0.98  inst_num_in_unprocessed:                9
% 1.53/0.98  inst_num_of_loops:                      0
% 1.53/0.98  inst_num_of_learning_restarts:          0
% 1.53/0.98  inst_num_moves_active_passive:          0
% 1.53/0.98  inst_lit_activity:                      0
% 1.53/0.98  inst_lit_activity_moves:                0
% 1.53/0.98  inst_num_tautologies:                   0
% 1.53/0.98  inst_num_prop_implied:                  0
% 1.53/0.98  inst_num_existing_simplified:           0
% 1.53/0.98  inst_num_eq_res_simplified:             0
% 1.53/0.98  inst_num_child_elim:                    0
% 1.53/0.98  inst_num_of_dismatching_blockings:      0
% 1.53/0.98  inst_num_of_non_proper_insts:           0
% 1.53/0.98  inst_num_of_duplicates:                 0
% 1.53/0.98  inst_inst_num_from_inst_to_res:         0
% 1.53/0.98  inst_dismatching_checking_time:         0.
% 1.53/0.98  
% 1.53/0.98  ------ Resolution
% 1.53/0.98  
% 1.53/0.98  res_num_of_clauses:                     0
% 1.53/0.98  res_num_in_passive:                     0
% 1.53/0.98  res_num_in_active:                      0
% 1.53/0.98  res_num_of_loops:                       56
% 1.53/0.98  res_forward_subset_subsumed:            0
% 1.53/0.98  res_backward_subset_subsumed:           0
% 1.53/0.98  res_forward_subsumed:                   2
% 1.53/0.98  res_backward_subsumed:                  6
% 1.53/0.98  res_forward_subsumption_resolution:     2
% 1.53/0.98  res_backward_subsumption_resolution:    0
% 1.53/0.98  res_clause_to_clause_subsumption:       163
% 1.53/0.98  res_orphan_elimination:                 0
% 1.53/0.98  res_tautology_del:                      26
% 1.53/0.98  res_num_eq_res_simplified:              4
% 1.53/0.98  res_num_sel_changes:                    0
% 1.53/0.98  res_moves_from_active_to_pass:          0
% 1.53/0.98  
% 1.53/0.98  ------ Superposition
% 1.53/0.98  
% 1.53/0.98  sup_time_total:                         0.
% 1.53/0.98  sup_time_generating:                    0.
% 1.53/0.98  sup_time_sim_full:                      0.
% 1.53/0.98  sup_time_sim_immed:                     0.
% 1.53/0.98  
% 1.53/0.98  sup_num_of_clauses:                     0
% 1.53/0.98  sup_num_in_active:                      0
% 1.53/0.98  sup_num_in_passive:                     0
% 1.53/0.98  sup_num_of_loops:                       0
% 1.53/0.98  sup_fw_superposition:                   0
% 1.53/0.98  sup_bw_superposition:                   0
% 1.53/0.98  sup_immediate_simplified:               0
% 1.53/0.98  sup_given_eliminated:                   0
% 1.53/0.98  comparisons_done:                       0
% 1.53/0.98  comparisons_avoided:                    0
% 1.53/0.98  
% 1.53/0.98  ------ Simplifications
% 1.53/0.98  
% 1.53/0.98  
% 1.53/0.98  sim_fw_subset_subsumed:                 0
% 1.53/0.98  sim_bw_subset_subsumed:                 0
% 1.53/0.98  sim_fw_subsumed:                        0
% 1.53/0.98  sim_bw_subsumed:                        0
% 1.53/0.98  sim_fw_subsumption_res:                 1
% 1.53/0.98  sim_bw_subsumption_res:                 0
% 1.53/0.98  sim_tautology_del:                      0
% 1.53/0.98  sim_eq_tautology_del:                   0
% 1.53/0.98  sim_eq_res_simp:                        0
% 1.53/0.98  sim_fw_demodulated:                     0
% 1.53/0.98  sim_bw_demodulated:                     0
% 1.53/0.98  sim_light_normalised:                   2
% 1.53/0.98  sim_joinable_taut:                      0
% 1.53/0.98  sim_joinable_simp:                      0
% 1.53/0.98  sim_ac_normalised:                      0
% 1.53/0.98  sim_smt_subsumption:                    0
% 1.53/0.98  
%------------------------------------------------------------------------------
