%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:15 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  241 (2017 expanded)
%              Number of clauses        :  155 ( 451 expanded)
%              Number of leaves         :   17 ( 554 expanded)
%              Depth                    :   33
%              Number of atoms          : 1507 (18070 expanded)
%              Number of equality atoms :  252 ( 592 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   26 (   6 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f47,f46,f45])).

fof(f74,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,(
    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f74,f59])).

fof(f75,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f88,plain,(
    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f75,f59])).

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

fof(f65,plain,(
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

fof(f84,plain,(
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
    inference(definition_unfolding,[],[f65,f59,f59,f59,f59])).

fof(f73,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f90,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(definition_unfolding,[],[f73,f59])).

fof(f72,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f55,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f48])).

fof(f87,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f76,f59])).

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

fof(f61,plain,(
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

fof(f80,plain,(
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
    inference(definition_unfolding,[],[f61,f59,f59,f59])).

fof(f79,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f42,plain,(
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

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f68,plain,(
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

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
      | ~ v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f68,f59,f59,f59,f59])).

fof(f78,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f42])).

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

fof(f57,plain,(
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

fof(f54,plain,(
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

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
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

fof(f85,plain,(
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
    inference(definition_unfolding,[],[f64,f59,f59,f59,f59])).

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

fof(f62,plain,(
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

fof(f83,plain,(
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
    inference(definition_unfolding,[],[f62,f59,f59,f59])).

fof(f63,plain,(
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

fof(f82,plain,(
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
    inference(definition_unfolding,[],[f63,f59,f59,f59])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4422,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_24,negated_conjecture,
    ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_23,negated_conjecture,
    ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f84])).

cnf(c_25,negated_conjecture,
    ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_435,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_436,plain,
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
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_440,plain,
    ( v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_26])).

cnf(c_441,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_440])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_653,plain,
    ( l1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_654,plain,
    ( l1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_1469,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(X1,X0,sK1))
    | v2_struct_0(X1)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_441,c_654])).

cnf(c_1470,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v2_struct_0(sK0)
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(unflattening,[status(thm)],[c_1469])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1474,plain,
    ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1470,c_29])).

cnf(c_1475,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(renaming,[status(thm)],[c_1474])).

cnf(c_1915,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_1475])).

cnf(c_2193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_1915])).

cnf(c_3094,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
    inference(equality_resolution_simp,[status(thm)],[c_2193])).

cnf(c_4408,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3094])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1391,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_654])).

cnf(c_1392,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_1391])).

cnf(c_4513,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,X0,sK1)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4408,c_1392])).

cnf(c_5064,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4513])).

cnf(c_5532,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5064])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_10,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_19,negated_conjecture,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_226,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_19])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_558,plain,
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
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_559,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(c_563,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_559,c_29,c_27])).

cnf(c_982,plain,
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
    inference(resolution_lifted,[status(thm)],[c_226,c_563])).

cnf(c_983,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_982])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_985,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_983,c_21])).

cnf(c_986,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_985])).

cnf(c_1022,plain,
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
    inference(resolution_lifted,[status(thm)],[c_10,c_986])).

cnf(c_1023,plain,
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
    inference(unflattening,[status(thm)],[c_1022])).

cnf(c_73,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1027,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1023,c_29,c_27,c_73])).

cnf(c_1870,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1027,c_23])).

cnf(c_1871,plain,
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
    inference(unflattening,[status(thm)],[c_1870])).

cnf(c_1875,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1871,c_26])).

cnf(c_1876,plain,
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
    inference(renaming,[status(thm)],[c_1875])).

cnf(c_2219,plain,
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
    inference(resolution_lifted,[status(thm)],[c_24,c_1876])).

cnf(c_3090,plain,
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
    inference(equality_resolution_simp,[status(thm)],[c_2219])).

cnf(c_3913,plain,
    ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3090])).

cnf(c_4409,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
    | r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3913])).

cnf(c_18,plain,
    ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_474,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_475,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(sK1)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_479,plain,
    ( ~ l1_struct_0(X0)
    | v2_struct_0(X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_475,c_26])).

cnf(c_480,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(renaming,[status(thm)],[c_479])).

cnf(c_1380,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
    | v2_struct_0(X0)
    | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_480,c_654])).

cnf(c_1381,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
    | v2_struct_0(sK0)
    | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(unflattening,[status(thm)],[c_1380])).

cnf(c_1383,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
    | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1381,c_29,c_24,c_23,c_22])).

cnf(c_3098,plain,
    ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_1383])).

cnf(c_4526,plain,
    ( r1_waybel_7(sK0,sK1,sK2) != iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4409,c_3098])).

cnf(c_20,negated_conjecture,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_228,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(prop_impl,[status(thm)],[c_20])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f66])).

cnf(c_525,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_526,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_530,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
    | ~ r3_waybel_9(sK0,X0,X1)
    | ~ l1_waybel_0(X0,sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ v7_waybel_0(X0)
    | ~ v4_orders_2(X0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_29,c_27])).

cnf(c_956,plain,
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
    inference(resolution_lifted,[status(thm)],[c_228,c_530])).

cnf(c_957,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(unflattening,[status(thm)],[c_956])).

cnf(c_959,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r1_waybel_7(sK0,sK1,sK2)
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_957,c_21])).

cnf(c_960,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_959])).

cnf(c_1070,plain,
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
    inference(resolution_lifted,[status(thm)],[c_10,c_960])).

cnf(c_1071,plain,
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
    inference(unflattening,[status(thm)],[c_1070])).

cnf(c_1075,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1071,c_29,c_27,c_73])).

cnf(c_1825,plain,
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
    inference(resolution_lifted,[status(thm)],[c_1075,c_23])).

cnf(c_1826,plain,
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
    inference(unflattening,[status(thm)],[c_1825])).

cnf(c_1830,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_1826,c_26])).

cnf(c_1831,plain,
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
    inference(renaming,[status(thm)],[c_1830])).

cnf(c_2257,plain,
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
    inference(resolution_lifted,[status(thm)],[c_24,c_1831])).

cnf(c_3086,plain,
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
    inference(equality_resolution_simp,[status(thm)],[c_2257])).

cnf(c_3914,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r1_waybel_7(sK0,sK1,sK2)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3086])).

cnf(c_4411,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
    | r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3914])).

cnf(c_4502,plain,
    ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4411,c_3098])).

cnf(c_4532,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4526,c_4502])).

cnf(c_4420,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4433,plain,
    ( m1_subset_1(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4420,c_1392])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_28])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_617,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_29,c_27])).

cnf(c_4415,plain,
    ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_4448,plain,
    ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4415,c_1392])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_connsp_2(X1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X3)
    | X0 != X4
    | k1_connsp_2(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_405,c_28])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_596,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_592,c_29,c_27])).

cnf(c_4416,plain,
    ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_4459,plain,
    ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4416,c_1392])).

cnf(c_4680,plain,
    ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4448,c_4459])).

cnf(c_5126,plain,
    ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4433,c_4680])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f85])).

cnf(c_13,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_169,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_13])).

cnf(c_170,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_169])).

cnf(c_1396,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v2_struct_0(X2)
    | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_170,c_654])).

cnf(c_1397,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1396])).

cnf(c_1401,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1397,c_29])).

cnf(c_1402,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1401])).

cnf(c_1795,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1402,c_23])).

cnf(c_1796,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1795])).

cnf(c_1800,plain,
    ( v1_xboole_0(X0)
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1796,c_26])).

cnf(c_1801,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1800])).

cnf(c_2295,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_1801])).

cnf(c_3082,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2295])).

cnf(c_4413,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,X0,sK1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3082])).

cnf(c_4477,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,X0,sK1)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4413,c_1392])).

cnf(c_4985,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4477])).

cnf(c_5431,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4985,c_37,c_5126])).

cnf(c_5432,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5431])).

cnf(c_3912,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v1_xboole_0(X0)
    | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3090])).

cnf(c_4410,plain,
    ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3912])).

cnf(c_4488,plain,
    ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4410,c_1392])).

cnf(c_4994,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4488])).

cnf(c_5437,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4994])).

cnf(c_5439,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5437,c_37,c_5126])).

cnf(c_12,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1429,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | v4_orders_2(k3_yellow19(X2,X1,X0))
    | v2_struct_0(X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_654])).

cnf(c_1430,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v2_struct_0(sK0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_1429])).

cnf(c_1434,plain,
    ( v4_orders_2(k3_yellow19(sK0,X1,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1430,c_29])).

cnf(c_1435,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_1434])).

cnf(c_1765,plain,
    ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_orders_2(k3_yellow19(sK0,X1,X0))
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1435,c_23])).

cnf(c_1766,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(unflattening,[status(thm)],[c_1765])).

cnf(c_1770,plain,
    ( v1_xboole_0(X0)
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1766,c_26])).

cnf(c_1771,plain,
    ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(renaming,[status(thm)],[c_1770])).

cnf(c_2318,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_1771])).

cnf(c_3078,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
    | v4_orders_2(k3_yellow19(sK0,X0,sK1))
    | v1_xboole_0(X0)
    | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
    inference(equality_resolution_simp,[status(thm)],[c_2318])).

cnf(c_4414,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,X0,sK1)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3078])).

cnf(c_4466,plain,
    ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,X0,sK1)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4414,c_1392])).

cnf(c_5055,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_4466])).

cnf(c_5524,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
    | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5055,c_37,c_5126])).

cnf(c_5525,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5524])).

cnf(c_5534,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5532,c_37,c_4532,c_5126,c_5432,c_5439,c_5525])).

cnf(c_5539,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4422,c_5534])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4423,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5600,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5539,c_4423])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:38:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.13/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.00  
% 2.13/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.13/1.00  
% 2.13/1.00  ------  iProver source info
% 2.13/1.00  
% 2.13/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.13/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.13/1.00  git: non_committed_changes: false
% 2.13/1.00  git: last_make_outside_of_git: false
% 2.13/1.00  
% 2.13/1.00  ------ 
% 2.13/1.00  
% 2.13/1.00  ------ Input Options
% 2.13/1.00  
% 2.13/1.00  --out_options                           all
% 2.13/1.00  --tptp_safe_out                         true
% 2.13/1.00  --problem_path                          ""
% 2.13/1.00  --include_path                          ""
% 2.13/1.00  --clausifier                            res/vclausify_rel
% 2.13/1.00  --clausifier_options                    --mode clausify
% 2.13/1.00  --stdin                                 false
% 2.13/1.00  --stats_out                             all
% 2.13/1.00  
% 2.13/1.00  ------ General Options
% 2.13/1.00  
% 2.13/1.00  --fof                                   false
% 2.13/1.00  --time_out_real                         305.
% 2.13/1.00  --time_out_virtual                      -1.
% 2.13/1.00  --symbol_type_check                     false
% 2.13/1.00  --clausify_out                          false
% 2.13/1.00  --sig_cnt_out                           false
% 2.13/1.00  --trig_cnt_out                          false
% 2.13/1.00  --trig_cnt_out_tolerance                1.
% 2.13/1.00  --trig_cnt_out_sk_spl                   false
% 2.13/1.00  --abstr_cl_out                          false
% 2.13/1.00  
% 2.13/1.00  ------ Global Options
% 2.13/1.00  
% 2.13/1.00  --schedule                              default
% 2.13/1.00  --add_important_lit                     false
% 2.13/1.00  --prop_solver_per_cl                    1000
% 2.13/1.00  --min_unsat_core                        false
% 2.13/1.00  --soft_assumptions                      false
% 2.13/1.00  --soft_lemma_size                       3
% 2.13/1.00  --prop_impl_unit_size                   0
% 2.13/1.00  --prop_impl_unit                        []
% 2.13/1.00  --share_sel_clauses                     true
% 2.13/1.00  --reset_solvers                         false
% 2.13/1.00  --bc_imp_inh                            [conj_cone]
% 2.13/1.00  --conj_cone_tolerance                   3.
% 2.13/1.00  --extra_neg_conj                        none
% 2.13/1.00  --large_theory_mode                     true
% 2.13/1.00  --prolific_symb_bound                   200
% 2.13/1.00  --lt_threshold                          2000
% 2.13/1.00  --clause_weak_htbl                      true
% 2.13/1.00  --gc_record_bc_elim                     false
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing Options
% 2.13/1.00  
% 2.13/1.00  --preprocessing_flag                    true
% 2.13/1.00  --time_out_prep_mult                    0.1
% 2.13/1.00  --splitting_mode                        input
% 2.13/1.00  --splitting_grd                         true
% 2.13/1.00  --splitting_cvd                         false
% 2.13/1.00  --splitting_cvd_svl                     false
% 2.13/1.00  --splitting_nvd                         32
% 2.13/1.00  --sub_typing                            true
% 2.13/1.00  --prep_gs_sim                           true
% 2.13/1.00  --prep_unflatten                        true
% 2.13/1.00  --prep_res_sim                          true
% 2.13/1.00  --prep_upred                            true
% 2.13/1.00  --prep_sem_filter                       exhaustive
% 2.13/1.00  --prep_sem_filter_out                   false
% 2.13/1.00  --pred_elim                             true
% 2.13/1.00  --res_sim_input                         true
% 2.13/1.00  --eq_ax_congr_red                       true
% 2.13/1.00  --pure_diseq_elim                       true
% 2.13/1.00  --brand_transform                       false
% 2.13/1.00  --non_eq_to_eq                          false
% 2.13/1.00  --prep_def_merge                        true
% 2.13/1.00  --prep_def_merge_prop_impl              false
% 2.13/1.00  --prep_def_merge_mbd                    true
% 2.13/1.00  --prep_def_merge_tr_red                 false
% 2.13/1.00  --prep_def_merge_tr_cl                  false
% 2.13/1.00  --smt_preprocessing                     true
% 2.13/1.00  --smt_ac_axioms                         fast
% 2.13/1.00  --preprocessed_out                      false
% 2.13/1.00  --preprocessed_stats                    false
% 2.13/1.00  
% 2.13/1.00  ------ Abstraction refinement Options
% 2.13/1.00  
% 2.13/1.00  --abstr_ref                             []
% 2.13/1.00  --abstr_ref_prep                        false
% 2.13/1.00  --abstr_ref_until_sat                   false
% 2.13/1.00  --abstr_ref_sig_restrict                funpre
% 2.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/1.00  --abstr_ref_under                       []
% 2.13/1.00  
% 2.13/1.00  ------ SAT Options
% 2.13/1.00  
% 2.13/1.00  --sat_mode                              false
% 2.13/1.00  --sat_fm_restart_options                ""
% 2.13/1.00  --sat_gr_def                            false
% 2.13/1.00  --sat_epr_types                         true
% 2.13/1.00  --sat_non_cyclic_types                  false
% 2.13/1.00  --sat_finite_models                     false
% 2.13/1.00  --sat_fm_lemmas                         false
% 2.13/1.00  --sat_fm_prep                           false
% 2.13/1.00  --sat_fm_uc_incr                        true
% 2.13/1.00  --sat_out_model                         small
% 2.13/1.00  --sat_out_clauses                       false
% 2.13/1.00  
% 2.13/1.00  ------ QBF Options
% 2.13/1.00  
% 2.13/1.00  --qbf_mode                              false
% 2.13/1.00  --qbf_elim_univ                         false
% 2.13/1.00  --qbf_dom_inst                          none
% 2.13/1.00  --qbf_dom_pre_inst                      false
% 2.13/1.00  --qbf_sk_in                             false
% 2.13/1.00  --qbf_pred_elim                         true
% 2.13/1.00  --qbf_split                             512
% 2.13/1.00  
% 2.13/1.00  ------ BMC1 Options
% 2.13/1.00  
% 2.13/1.00  --bmc1_incremental                      false
% 2.13/1.00  --bmc1_axioms                           reachable_all
% 2.13/1.00  --bmc1_min_bound                        0
% 2.13/1.00  --bmc1_max_bound                        -1
% 2.13/1.00  --bmc1_max_bound_default                -1
% 2.13/1.00  --bmc1_symbol_reachability              true
% 2.13/1.00  --bmc1_property_lemmas                  false
% 2.13/1.00  --bmc1_k_induction                      false
% 2.13/1.00  --bmc1_non_equiv_states                 false
% 2.13/1.00  --bmc1_deadlock                         false
% 2.13/1.00  --bmc1_ucm                              false
% 2.13/1.00  --bmc1_add_unsat_core                   none
% 2.13/1.00  --bmc1_unsat_core_children              false
% 2.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/1.00  --bmc1_out_stat                         full
% 2.13/1.00  --bmc1_ground_init                      false
% 2.13/1.00  --bmc1_pre_inst_next_state              false
% 2.13/1.00  --bmc1_pre_inst_state                   false
% 2.13/1.00  --bmc1_pre_inst_reach_state             false
% 2.13/1.00  --bmc1_out_unsat_core                   false
% 2.13/1.00  --bmc1_aig_witness_out                  false
% 2.13/1.00  --bmc1_verbose                          false
% 2.13/1.00  --bmc1_dump_clauses_tptp                false
% 2.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.13/1.00  --bmc1_dump_file                        -
% 2.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.13/1.00  --bmc1_ucm_extend_mode                  1
% 2.13/1.00  --bmc1_ucm_init_mode                    2
% 2.13/1.00  --bmc1_ucm_cone_mode                    none
% 2.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.13/1.00  --bmc1_ucm_relax_model                  4
% 2.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/1.00  --bmc1_ucm_layered_model                none
% 2.13/1.00  --bmc1_ucm_max_lemma_size               10
% 2.13/1.00  
% 2.13/1.00  ------ AIG Options
% 2.13/1.00  
% 2.13/1.00  --aig_mode                              false
% 2.13/1.00  
% 2.13/1.00  ------ Instantiation Options
% 2.13/1.00  
% 2.13/1.00  --instantiation_flag                    true
% 2.13/1.00  --inst_sos_flag                         false
% 2.13/1.00  --inst_sos_phase                        true
% 2.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel_side                     num_symb
% 2.13/1.00  --inst_solver_per_active                1400
% 2.13/1.00  --inst_solver_calls_frac                1.
% 2.13/1.00  --inst_passive_queue_type               priority_queues
% 2.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/1.00  --inst_passive_queues_freq              [25;2]
% 2.13/1.00  --inst_dismatching                      true
% 2.13/1.00  --inst_eager_unprocessed_to_passive     true
% 2.13/1.00  --inst_prop_sim_given                   true
% 2.13/1.00  --inst_prop_sim_new                     false
% 2.13/1.00  --inst_subs_new                         false
% 2.13/1.00  --inst_eq_res_simp                      false
% 2.13/1.00  --inst_subs_given                       false
% 2.13/1.00  --inst_orphan_elimination               true
% 2.13/1.00  --inst_learning_loop_flag               true
% 2.13/1.00  --inst_learning_start                   3000
% 2.13/1.00  --inst_learning_factor                  2
% 2.13/1.00  --inst_start_prop_sim_after_learn       3
% 2.13/1.00  --inst_sel_renew                        solver
% 2.13/1.00  --inst_lit_activity_flag                true
% 2.13/1.00  --inst_restr_to_given                   false
% 2.13/1.00  --inst_activity_threshold               500
% 2.13/1.00  --inst_out_proof                        true
% 2.13/1.00  
% 2.13/1.00  ------ Resolution Options
% 2.13/1.00  
% 2.13/1.00  --resolution_flag                       true
% 2.13/1.00  --res_lit_sel                           adaptive
% 2.13/1.00  --res_lit_sel_side                      none
% 2.13/1.00  --res_ordering                          kbo
% 2.13/1.00  --res_to_prop_solver                    active
% 2.13/1.00  --res_prop_simpl_new                    false
% 2.13/1.00  --res_prop_simpl_given                  true
% 2.13/1.00  --res_passive_queue_type                priority_queues
% 2.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/1.00  --res_passive_queues_freq               [15;5]
% 2.13/1.00  --res_forward_subs                      full
% 2.13/1.00  --res_backward_subs                     full
% 2.13/1.00  --res_forward_subs_resolution           true
% 2.13/1.00  --res_backward_subs_resolution          true
% 2.13/1.00  --res_orphan_elimination                true
% 2.13/1.00  --res_time_limit                        2.
% 2.13/1.00  --res_out_proof                         true
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Options
% 2.13/1.00  
% 2.13/1.00  --superposition_flag                    true
% 2.13/1.00  --sup_passive_queue_type                priority_queues
% 2.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.13/1.00  --demod_completeness_check              fast
% 2.13/1.00  --demod_use_ground                      true
% 2.13/1.00  --sup_to_prop_solver                    passive
% 2.13/1.00  --sup_prop_simpl_new                    true
% 2.13/1.00  --sup_prop_simpl_given                  true
% 2.13/1.00  --sup_fun_splitting                     false
% 2.13/1.00  --sup_smt_interval                      50000
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Simplification Setup
% 2.13/1.00  
% 2.13/1.00  --sup_indices_passive                   []
% 2.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_full_bw                           [BwDemod]
% 2.13/1.00  --sup_immed_triv                        [TrivRules]
% 2.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_immed_bw_main                     []
% 2.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  
% 2.13/1.00  ------ Combination Options
% 2.13/1.00  
% 2.13/1.00  --comb_res_mult                         3
% 2.13/1.00  --comb_sup_mult                         2
% 2.13/1.00  --comb_inst_mult                        10
% 2.13/1.00  
% 2.13/1.00  ------ Debug Options
% 2.13/1.00  
% 2.13/1.00  --dbg_backtrace                         false
% 2.13/1.00  --dbg_dump_prop_clauses                 false
% 2.13/1.00  --dbg_dump_prop_clauses_file            -
% 2.13/1.00  --dbg_out_stat                          false
% 2.13/1.00  ------ Parsing...
% 2.13/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.13/1.00  ------ Proving...
% 2.13/1.00  ------ Problem Properties 
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  clauses                                 19
% 2.13/1.00  conjectures                             4
% 2.13/1.00  EPR                                     4
% 2.13/1.00  Horn                                    15
% 2.13/1.00  unary                                   7
% 2.13/1.00  binary                                  3
% 2.13/1.00  lits                                    59
% 2.13/1.00  lits eq                                 11
% 2.13/1.00  fd_pure                                 0
% 2.13/1.00  fd_pseudo                               0
% 2.13/1.00  fd_cond                                 0
% 2.13/1.00  fd_pseudo_cond                          1
% 2.13/1.00  AC symbols                              0
% 2.13/1.00  
% 2.13/1.00  ------ Schedule dynamic 5 is on 
% 2.13/1.00  
% 2.13/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  ------ 
% 2.13/1.00  Current options:
% 2.13/1.00  ------ 
% 2.13/1.00  
% 2.13/1.00  ------ Input Options
% 2.13/1.00  
% 2.13/1.00  --out_options                           all
% 2.13/1.00  --tptp_safe_out                         true
% 2.13/1.00  --problem_path                          ""
% 2.13/1.00  --include_path                          ""
% 2.13/1.00  --clausifier                            res/vclausify_rel
% 2.13/1.00  --clausifier_options                    --mode clausify
% 2.13/1.00  --stdin                                 false
% 2.13/1.00  --stats_out                             all
% 2.13/1.00  
% 2.13/1.00  ------ General Options
% 2.13/1.00  
% 2.13/1.00  --fof                                   false
% 2.13/1.00  --time_out_real                         305.
% 2.13/1.00  --time_out_virtual                      -1.
% 2.13/1.00  --symbol_type_check                     false
% 2.13/1.00  --clausify_out                          false
% 2.13/1.00  --sig_cnt_out                           false
% 2.13/1.00  --trig_cnt_out                          false
% 2.13/1.00  --trig_cnt_out_tolerance                1.
% 2.13/1.00  --trig_cnt_out_sk_spl                   false
% 2.13/1.00  --abstr_cl_out                          false
% 2.13/1.00  
% 2.13/1.00  ------ Global Options
% 2.13/1.00  
% 2.13/1.00  --schedule                              default
% 2.13/1.00  --add_important_lit                     false
% 2.13/1.00  --prop_solver_per_cl                    1000
% 2.13/1.00  --min_unsat_core                        false
% 2.13/1.00  --soft_assumptions                      false
% 2.13/1.00  --soft_lemma_size                       3
% 2.13/1.00  --prop_impl_unit_size                   0
% 2.13/1.00  --prop_impl_unit                        []
% 2.13/1.00  --share_sel_clauses                     true
% 2.13/1.00  --reset_solvers                         false
% 2.13/1.00  --bc_imp_inh                            [conj_cone]
% 2.13/1.00  --conj_cone_tolerance                   3.
% 2.13/1.00  --extra_neg_conj                        none
% 2.13/1.00  --large_theory_mode                     true
% 2.13/1.00  --prolific_symb_bound                   200
% 2.13/1.00  --lt_threshold                          2000
% 2.13/1.00  --clause_weak_htbl                      true
% 2.13/1.00  --gc_record_bc_elim                     false
% 2.13/1.00  
% 2.13/1.00  ------ Preprocessing Options
% 2.13/1.00  
% 2.13/1.00  --preprocessing_flag                    true
% 2.13/1.00  --time_out_prep_mult                    0.1
% 2.13/1.00  --splitting_mode                        input
% 2.13/1.00  --splitting_grd                         true
% 2.13/1.00  --splitting_cvd                         false
% 2.13/1.00  --splitting_cvd_svl                     false
% 2.13/1.00  --splitting_nvd                         32
% 2.13/1.00  --sub_typing                            true
% 2.13/1.00  --prep_gs_sim                           true
% 2.13/1.00  --prep_unflatten                        true
% 2.13/1.00  --prep_res_sim                          true
% 2.13/1.00  --prep_upred                            true
% 2.13/1.00  --prep_sem_filter                       exhaustive
% 2.13/1.00  --prep_sem_filter_out                   false
% 2.13/1.00  --pred_elim                             true
% 2.13/1.00  --res_sim_input                         true
% 2.13/1.00  --eq_ax_congr_red                       true
% 2.13/1.00  --pure_diseq_elim                       true
% 2.13/1.00  --brand_transform                       false
% 2.13/1.00  --non_eq_to_eq                          false
% 2.13/1.00  --prep_def_merge                        true
% 2.13/1.00  --prep_def_merge_prop_impl              false
% 2.13/1.00  --prep_def_merge_mbd                    true
% 2.13/1.00  --prep_def_merge_tr_red                 false
% 2.13/1.00  --prep_def_merge_tr_cl                  false
% 2.13/1.00  --smt_preprocessing                     true
% 2.13/1.00  --smt_ac_axioms                         fast
% 2.13/1.00  --preprocessed_out                      false
% 2.13/1.00  --preprocessed_stats                    false
% 2.13/1.00  
% 2.13/1.00  ------ Abstraction refinement Options
% 2.13/1.00  
% 2.13/1.00  --abstr_ref                             []
% 2.13/1.00  --abstr_ref_prep                        false
% 2.13/1.00  --abstr_ref_until_sat                   false
% 2.13/1.00  --abstr_ref_sig_restrict                funpre
% 2.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.13/1.00  --abstr_ref_under                       []
% 2.13/1.00  
% 2.13/1.00  ------ SAT Options
% 2.13/1.00  
% 2.13/1.00  --sat_mode                              false
% 2.13/1.00  --sat_fm_restart_options                ""
% 2.13/1.00  --sat_gr_def                            false
% 2.13/1.00  --sat_epr_types                         true
% 2.13/1.00  --sat_non_cyclic_types                  false
% 2.13/1.00  --sat_finite_models                     false
% 2.13/1.00  --sat_fm_lemmas                         false
% 2.13/1.00  --sat_fm_prep                           false
% 2.13/1.00  --sat_fm_uc_incr                        true
% 2.13/1.00  --sat_out_model                         small
% 2.13/1.00  --sat_out_clauses                       false
% 2.13/1.00  
% 2.13/1.00  ------ QBF Options
% 2.13/1.00  
% 2.13/1.00  --qbf_mode                              false
% 2.13/1.00  --qbf_elim_univ                         false
% 2.13/1.00  --qbf_dom_inst                          none
% 2.13/1.00  --qbf_dom_pre_inst                      false
% 2.13/1.00  --qbf_sk_in                             false
% 2.13/1.00  --qbf_pred_elim                         true
% 2.13/1.00  --qbf_split                             512
% 2.13/1.00  
% 2.13/1.00  ------ BMC1 Options
% 2.13/1.00  
% 2.13/1.00  --bmc1_incremental                      false
% 2.13/1.00  --bmc1_axioms                           reachable_all
% 2.13/1.00  --bmc1_min_bound                        0
% 2.13/1.00  --bmc1_max_bound                        -1
% 2.13/1.00  --bmc1_max_bound_default                -1
% 2.13/1.00  --bmc1_symbol_reachability              true
% 2.13/1.00  --bmc1_property_lemmas                  false
% 2.13/1.00  --bmc1_k_induction                      false
% 2.13/1.00  --bmc1_non_equiv_states                 false
% 2.13/1.00  --bmc1_deadlock                         false
% 2.13/1.00  --bmc1_ucm                              false
% 2.13/1.00  --bmc1_add_unsat_core                   none
% 2.13/1.00  --bmc1_unsat_core_children              false
% 2.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.13/1.00  --bmc1_out_stat                         full
% 2.13/1.00  --bmc1_ground_init                      false
% 2.13/1.00  --bmc1_pre_inst_next_state              false
% 2.13/1.00  --bmc1_pre_inst_state                   false
% 2.13/1.00  --bmc1_pre_inst_reach_state             false
% 2.13/1.00  --bmc1_out_unsat_core                   false
% 2.13/1.00  --bmc1_aig_witness_out                  false
% 2.13/1.00  --bmc1_verbose                          false
% 2.13/1.00  --bmc1_dump_clauses_tptp                false
% 2.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.13/1.00  --bmc1_dump_file                        -
% 2.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.13/1.00  --bmc1_ucm_extend_mode                  1
% 2.13/1.00  --bmc1_ucm_init_mode                    2
% 2.13/1.00  --bmc1_ucm_cone_mode                    none
% 2.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.13/1.00  --bmc1_ucm_relax_model                  4
% 2.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.13/1.00  --bmc1_ucm_layered_model                none
% 2.13/1.00  --bmc1_ucm_max_lemma_size               10
% 2.13/1.00  
% 2.13/1.00  ------ AIG Options
% 2.13/1.00  
% 2.13/1.00  --aig_mode                              false
% 2.13/1.00  
% 2.13/1.00  ------ Instantiation Options
% 2.13/1.00  
% 2.13/1.00  --instantiation_flag                    true
% 2.13/1.00  --inst_sos_flag                         false
% 2.13/1.00  --inst_sos_phase                        true
% 2.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.13/1.00  --inst_lit_sel_side                     none
% 2.13/1.00  --inst_solver_per_active                1400
% 2.13/1.00  --inst_solver_calls_frac                1.
% 2.13/1.00  --inst_passive_queue_type               priority_queues
% 2.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.13/1.00  --inst_passive_queues_freq              [25;2]
% 2.13/1.00  --inst_dismatching                      true
% 2.13/1.00  --inst_eager_unprocessed_to_passive     true
% 2.13/1.00  --inst_prop_sim_given                   true
% 2.13/1.00  --inst_prop_sim_new                     false
% 2.13/1.00  --inst_subs_new                         false
% 2.13/1.00  --inst_eq_res_simp                      false
% 2.13/1.00  --inst_subs_given                       false
% 2.13/1.00  --inst_orphan_elimination               true
% 2.13/1.00  --inst_learning_loop_flag               true
% 2.13/1.00  --inst_learning_start                   3000
% 2.13/1.00  --inst_learning_factor                  2
% 2.13/1.00  --inst_start_prop_sim_after_learn       3
% 2.13/1.00  --inst_sel_renew                        solver
% 2.13/1.00  --inst_lit_activity_flag                true
% 2.13/1.00  --inst_restr_to_given                   false
% 2.13/1.00  --inst_activity_threshold               500
% 2.13/1.00  --inst_out_proof                        true
% 2.13/1.00  
% 2.13/1.00  ------ Resolution Options
% 2.13/1.00  
% 2.13/1.00  --resolution_flag                       false
% 2.13/1.00  --res_lit_sel                           adaptive
% 2.13/1.00  --res_lit_sel_side                      none
% 2.13/1.00  --res_ordering                          kbo
% 2.13/1.00  --res_to_prop_solver                    active
% 2.13/1.00  --res_prop_simpl_new                    false
% 2.13/1.00  --res_prop_simpl_given                  true
% 2.13/1.00  --res_passive_queue_type                priority_queues
% 2.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.13/1.00  --res_passive_queues_freq               [15;5]
% 2.13/1.00  --res_forward_subs                      full
% 2.13/1.00  --res_backward_subs                     full
% 2.13/1.00  --res_forward_subs_resolution           true
% 2.13/1.00  --res_backward_subs_resolution          true
% 2.13/1.00  --res_orphan_elimination                true
% 2.13/1.00  --res_time_limit                        2.
% 2.13/1.00  --res_out_proof                         true
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Options
% 2.13/1.00  
% 2.13/1.00  --superposition_flag                    true
% 2.13/1.00  --sup_passive_queue_type                priority_queues
% 2.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.13/1.00  --demod_completeness_check              fast
% 2.13/1.00  --demod_use_ground                      true
% 2.13/1.00  --sup_to_prop_solver                    passive
% 2.13/1.00  --sup_prop_simpl_new                    true
% 2.13/1.00  --sup_prop_simpl_given                  true
% 2.13/1.00  --sup_fun_splitting                     false
% 2.13/1.00  --sup_smt_interval                      50000
% 2.13/1.00  
% 2.13/1.00  ------ Superposition Simplification Setup
% 2.13/1.00  
% 2.13/1.00  --sup_indices_passive                   []
% 2.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_full_bw                           [BwDemod]
% 2.13/1.00  --sup_immed_triv                        [TrivRules]
% 2.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_immed_bw_main                     []
% 2.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.13/1.00  
% 2.13/1.00  ------ Combination Options
% 2.13/1.00  
% 2.13/1.00  --comb_res_mult                         3
% 2.13/1.00  --comb_sup_mult                         2
% 2.13/1.00  --comb_inst_mult                        10
% 2.13/1.00  
% 2.13/1.00  ------ Debug Options
% 2.13/1.00  
% 2.13/1.00  --dbg_backtrace                         false
% 2.13/1.00  --dbg_dump_prop_clauses                 false
% 2.13/1.00  --dbg_dump_prop_clauses_file            -
% 2.13/1.00  --dbg_out_stat                          false
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  ------ Proving...
% 2.13/1.00  
% 2.13/1.00  
% 2.13/1.00  % SZS status Theorem for theBenchmark.p
% 2.13/1.00  
% 2.13/1.00   Resolution empty clause
% 2.13/1.00  
% 2.13/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.13/1.00  
% 2.13/1.00  fof(f2,axiom,(
% 2.13/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f41,plain,(
% 2.13/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.13/1.00    inference(nnf_transformation,[],[f2])).
% 2.13/1.00  
% 2.13/1.00  fof(f53,plain,(
% 2.13/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f41])).
% 2.13/1.00  
% 2.13/1.00  fof(f14,conjecture,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f15,negated_conjecture,(
% 2.13/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 2.13/1.00    inference(negated_conjecture,[],[f14])).
% 2.13/1.00  
% 2.13/1.00  fof(f37,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f15])).
% 2.13/1.00  
% 2.13/1.00  fof(f38,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f37])).
% 2.13/1.00  
% 2.13/1.00  fof(f43,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : (((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/1.00    inference(nnf_transformation,[],[f38])).
% 2.13/1.00  
% 2.13/1.00  fof(f44,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f43])).
% 2.13/1.00  
% 2.13/1.00  fof(f47,plain,(
% 2.13/1.00    ( ! [X0,X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => ((~r1_waybel_7(X0,X1,sK2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & (r1_waybel_7(X0,X1,sK2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),sK2)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f46,plain,(
% 2.13/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => (? [X2] : ((~r1_waybel_7(X0,sK1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & (r1_waybel_7(X0,sK1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),sK1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(sK1))) )),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f45,plain,(
% 2.13/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r1_waybel_7(X0,X1,X2) | ~r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & (r1_waybel_7(X0,X1,X2) | r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_waybel_7(sK0,X1,X2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & (r1_waybel_7(sK0,X1,X2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X1),X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 2.13/1.00    introduced(choice_axiom,[])).
% 2.13/1.00  
% 2.13/1.00  fof(f48,plain,(
% 2.13/1.00    (((~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & (r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) & v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 2.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f47,f46,f45])).
% 2.13/1.00  
% 2.13/1.00  fof(f74,plain,(
% 2.13/1.00    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 2.13/1.00    inference(cnf_transformation,[],[f48])).
% 2.13/1.00  
% 2.13/1.00  fof(f8,axiom,(
% 2.13/1.00    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f59,plain,(
% 2.13/1.00    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 2.13/1.00    inference(cnf_transformation,[],[f8])).
% 2.13/1.00  
% 2.13/1.00  fof(f89,plain,(
% 2.13/1.00    v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 2.13/1.00    inference(definition_unfolding,[],[f74,f59])).
% 2.13/1.00  
% 2.13/1.00  fof(f75,plain,(
% 2.13/1.00    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 2.13/1.00    inference(cnf_transformation,[],[f48])).
% 2.13/1.00  
% 2.13/1.00  fof(f88,plain,(
% 2.13/1.00    v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 2.13/1.00    inference(definition_unfolding,[],[f75,f59])).
% 2.13/1.00  
% 2.13/1.00  fof(f11,axiom,(
% 2.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f17,plain,(
% 2.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.13/1.00    inference(pure_predicate_removal,[],[f11])).
% 2.13/1.00  
% 2.13/1.00  fof(f31,plain,(
% 2.13/1.00    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f17])).
% 2.13/1.00  
% 2.13/1.00  fof(f32,plain,(
% 2.13/1.00    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f31])).
% 2.13/1.00  
% 2.13/1.00  fof(f65,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f32])).
% 2.13/1.00  
% 2.13/1.00  fof(f84,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(definition_unfolding,[],[f65,f59,f59,f59,f59])).
% 2.13/1.00  
% 2.13/1.00  fof(f73,plain,(
% 2.13/1.00    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 2.13/1.00    inference(cnf_transformation,[],[f48])).
% 2.13/1.00  
% 2.13/1.00  fof(f90,plain,(
% 2.13/1.00    v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))),
% 2.13/1.00    inference(definition_unfolding,[],[f73,f59])).
% 2.13/1.00  
% 2.13/1.00  fof(f72,plain,(
% 2.13/1.00    ~v1_xboole_0(sK1)),
% 2.13/1.00    inference(cnf_transformation,[],[f48])).
% 2.13/1.00  
% 2.13/1.00  fof(f5,axiom,(
% 2.13/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f22,plain,(
% 2.13/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.13/1.00    inference(ennf_transformation,[],[f5])).
% 2.13/1.00  
% 2.13/1.00  fof(f56,plain,(
% 2.13/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f22])).
% 2.13/1.00  
% 2.13/1.00  fof(f71,plain,(
% 2.13/1.00    l1_pre_topc(sK0)),
% 2.13/1.00    inference(cnf_transformation,[],[f48])).
% 2.13/1.00  
% 2.13/1.00  fof(f69,plain,(
% 2.13/1.00    ~v2_struct_0(sK0)),
% 2.13/1.00    inference(cnf_transformation,[],[f48])).
% 2.13/1.00  
% 2.13/1.00  fof(f4,axiom,(
% 2.13/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f21,plain,(
% 2.13/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.13/1.00    inference(ennf_transformation,[],[f4])).
% 2.13/1.00  
% 2.13/1.00  fof(f55,plain,(
% 2.13/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f21])).
% 2.13/1.00  
% 2.13/1.00  fof(f76,plain,(
% 2.13/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 2.13/1.00    inference(cnf_transformation,[],[f48])).
% 2.13/1.00  
% 2.13/1.00  fof(f87,plain,(
% 2.13/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 2.13/1.00    inference(definition_unfolding,[],[f76,f59])).
% 2.13/1.00  
% 2.13/1.00  fof(f9,axiom,(
% 2.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f18,plain,(
% 2.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.13/1.00    inference(pure_predicate_removal,[],[f9])).
% 2.13/1.00  
% 2.13/1.00  fof(f27,plain,(
% 2.13/1.00    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f18])).
% 2.13/1.00  
% 2.13/1.00  fof(f28,plain,(
% 2.13/1.00    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f27])).
% 2.13/1.00  
% 2.13/1.00  fof(f61,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f28])).
% 2.13/1.00  
% 2.13/1.00  fof(f80,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(definition_unfolding,[],[f61,f59,f59,f59])).
% 2.13/1.00  
% 2.13/1.00  fof(f79,plain,(
% 2.13/1.00    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 2.13/1.00    inference(cnf_transformation,[],[f48])).
% 2.13/1.00  
% 2.13/1.00  fof(f12,axiom,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f33,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f12])).
% 2.13/1.00  
% 2.13/1.00  fof(f34,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f33])).
% 2.13/1.00  
% 2.13/1.00  fof(f42,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (! [X2] : (((r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) & (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(nnf_transformation,[],[f34])).
% 2.13/1.00  
% 2.13/1.00  fof(f67,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (r3_waybel_9(X0,X1,X2) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f70,plain,(
% 2.13/1.00    v2_pre_topc(sK0)),
% 2.13/1.00    inference(cnf_transformation,[],[f48])).
% 2.13/1.00  
% 2.13/1.00  fof(f77,plain,(
% 2.13/1.00    m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.13/1.00    inference(cnf_transformation,[],[f48])).
% 2.13/1.00  
% 2.13/1.00  fof(f13,axiom,(
% 2.13/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f35,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f13])).
% 2.13/1.00  
% 2.13/1.00  fof(f36,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f35])).
% 2.13/1.00  
% 2.13/1.00  fof(f68,plain,(
% 2.13/1.00    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f36])).
% 2.13/1.00  
% 2.13/1.00  fof(f86,plain,(
% 2.13/1.00    ( ! [X0,X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))))) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_lattice3(k1_lattice3(k2_struct_0(X0)))) | ~v1_subset_1(X1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(definition_unfolding,[],[f68,f59,f59,f59,f59])).
% 2.13/1.00  
% 2.13/1.00  fof(f78,plain,(
% 2.13/1.00    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 2.13/1.00    inference(cnf_transformation,[],[f48])).
% 2.13/1.00  
% 2.13/1.00  fof(f66,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f42])).
% 2.13/1.00  
% 2.13/1.00  fof(f6,axiom,(
% 2.13/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f23,plain,(
% 2.13/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f6])).
% 2.13/1.00  
% 2.13/1.00  fof(f24,plain,(
% 2.13/1.00    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f23])).
% 2.13/1.00  
% 2.13/1.00  fof(f57,plain,(
% 2.13/1.00    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f24])).
% 2.13/1.00  
% 2.13/1.00  fof(f3,axiom,(
% 2.13/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f20,plain,(
% 2.13/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.13/1.00    inference(ennf_transformation,[],[f3])).
% 2.13/1.00  
% 2.13/1.00  fof(f54,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f20])).
% 2.13/1.00  
% 2.13/1.00  fof(f7,axiom,(
% 2.13/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f25,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f7])).
% 2.13/1.00  
% 2.13/1.00  fof(f26,plain,(
% 2.13/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f25])).
% 2.13/1.00  
% 2.13/1.00  fof(f58,plain,(
% 2.13/1.00    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f26])).
% 2.13/1.00  
% 2.13/1.00  fof(f64,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f32])).
% 2.13/1.00  
% 2.13/1.00  fof(f85,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v1_subset_1(X2,u1_struct_0(k3_lattice3(k1_lattice3(X1)))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(definition_unfolding,[],[f64,f59,f59,f59,f59])).
% 2.13/1.00  
% 2.13/1.00  fof(f10,axiom,(
% 2.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f16,plain,(
% 2.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.13/1.00    inference(pure_predicate_removal,[],[f10])).
% 2.13/1.00  
% 2.13/1.00  fof(f19,plain,(
% 2.13/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 2.13/1.00    inference(pure_predicate_removal,[],[f16])).
% 2.13/1.00  
% 2.13/1.00  fof(f29,plain,(
% 2.13/1.00    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.13/1.00    inference(ennf_transformation,[],[f19])).
% 2.13/1.00  
% 2.13/1.00  fof(f30,plain,(
% 2.13/1.00    ! [X0,X1,X2] : ((v4_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.13/1.00    inference(flattening,[],[f29])).
% 2.13/1.00  
% 2.13/1.00  fof(f62,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f30])).
% 2.13/1.00  
% 2.13/1.00  fof(f83,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (~v2_struct_0(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(definition_unfolding,[],[f62,f59,f59,f59])).
% 2.13/1.00  
% 2.13/1.00  fof(f63,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(cnf_transformation,[],[f30])).
% 2.13/1.00  
% 2.13/1.00  fof(f82,plain,(
% 2.13/1.00    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1))))) | ~v13_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | ~v2_waybel_0(X2,k3_lattice3(k1_lattice3(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.13/1.00    inference(definition_unfolding,[],[f63,f59,f59,f59])).
% 2.13/1.00  
% 2.13/1.00  fof(f1,axiom,(
% 2.13/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.13/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.13/1.00  
% 2.13/1.00  fof(f39,plain,(
% 2.13/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.13/1.00    inference(nnf_transformation,[],[f1])).
% 2.13/1.00  
% 2.13/1.00  fof(f40,plain,(
% 2.13/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.13/1.00    inference(flattening,[],[f39])).
% 2.13/1.00  
% 2.13/1.00  fof(f49,plain,(
% 2.13/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.13/1.00    inference(cnf_transformation,[],[f40])).
% 2.13/1.00  
% 2.13/1.00  fof(f92,plain,(
% 2.13/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.13/1.00    inference(equality_resolution,[],[f49])).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3,plain,
% 2.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_4422,plain,
% 2.13/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.13/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_24,negated_conjecture,
% 2.13/1.00      ( v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.13/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_23,negated_conjecture,
% 2.13/1.00      ( v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.13/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_14,plain,
% 2.13/1.00      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.13/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.00      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.13/1.00      | v2_struct_0(X2)
% 2.13/1.00      | ~ l1_struct_0(X2)
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | v1_xboole_0(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_25,negated_conjecture,
% 2.13/1.00      ( v1_subset_1(sK1,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))) ),
% 2.13/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_435,plain,
% 2.13/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.00      | v7_waybel_0(k3_yellow19(X2,X1,X0))
% 2.13/1.00      | v2_struct_0(X2)
% 2.13/1.00      | ~ l1_struct_0(X2)
% 2.13/1.00      | v1_xboole_0(X1)
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | sK1 != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_436,plain,
% 2.13/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ l1_struct_0(X1)
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | v1_xboole_0(sK1)
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_435]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_26,negated_conjecture,
% 2.13/1.00      ( ~ v1_xboole_0(sK1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_440,plain,
% 2.13/1.00      ( v1_xboole_0(X0)
% 2.13/1.00      | ~ l1_struct_0(X1)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 2.13/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.13/1.00      inference(global_propositional_subsumption,[status(thm)],[c_436,c_26]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_441,plain,
% 2.13/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ l1_struct_0(X1)
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.13/1.00      inference(renaming,[status(thm)],[c_440]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_7,plain,
% 2.13/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_27,negated_conjecture,
% 2.13/1.00      ( l1_pre_topc(sK0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_653,plain,
% 2.13/1.00      ( l1_struct_0(X0) | sK0 != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_654,plain,
% 2.13/1.00      ( l1_struct_0(sK0) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_653]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1469,plain,
% 2.13/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.00      | v7_waybel_0(k3_yellow19(X1,X0,sK1))
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | sK0 != X1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_441,c_654]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1470,plain,
% 2.13/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.13/1.00      | v2_struct_0(sK0)
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1469]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_29,negated_conjecture,
% 2.13/1.00      ( ~ v2_struct_0(sK0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1474,plain,
% 2.13/1.00      ( v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.13/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.13/1.00      inference(global_propositional_subsumption,[status(thm)],[c_1470,c_29]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1475,plain,
% 2.13/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.13/1.00      inference(renaming,[status(thm)],[c_1474]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1915,plain,
% 2.13/1.00      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | sK1 != sK1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_1475]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_2193,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | sK1 != sK1 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_1915]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_3094,plain,
% 2.13/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1))
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0))) ),
% 2.13/1.00      inference(equality_resolution_simp,[status(thm)],[c_2193]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_4408,plain,
% 2.13/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.13/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.13/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1)) = iProver_top
% 2.13/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_3094]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_6,plain,
% 2.13/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1391,plain,
% 2.13/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_654]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1392,plain,
% 2.13/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1391]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_4513,plain,
% 2.13/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.00      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(X0)))
% 2.13/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.13/1.00      | v7_waybel_0(k3_yellow19(sK0,X0,sK1)) = iProver_top
% 2.13/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.13/1.00      inference(light_normalisation,[status(thm)],[c_4408,c_1392]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_5064,plain,
% 2.13/1.00      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.13/1.00      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 2.13/1.00      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 2.13/1.00      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 2.13/1.00      inference(equality_resolution,[status(thm)],[c_4513]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_5532,plain,
% 2.13/1.00      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 2.13/1.00      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 2.13/1.00      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 2.13/1.00      inference(equality_resolution_simp,[status(thm)],[c_5064]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_22,negated_conjecture,
% 2.13/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
% 2.13/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_37,plain,
% 2.13/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) = iProver_top ),
% 2.13/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_10,plain,
% 2.13/1.00      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | l1_waybel_0(k3_yellow19(X2,X1,X0),X2)
% 2.13/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.00      | v2_struct_0(X2)
% 2.13/1.00      | ~ l1_struct_0(X2)
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | v1_xboole_0(X1) ),
% 2.13/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_19,negated_conjecture,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.00      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 2.13/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_226,plain,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.00      | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 2.13/1.00      inference(prop_impl,[status(thm)],[c_19]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_16,plain,
% 2.13/1.00      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.13/1.00      | r3_waybel_9(X0,X1,X2)
% 2.13/1.00      | ~ l1_waybel_0(X1,X0)
% 2.13/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.13/1.00      | ~ v7_waybel_0(X1)
% 2.13/1.00      | ~ v4_orders_2(X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ v2_pre_topc(X0)
% 2.13/1.00      | ~ l1_pre_topc(X0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_28,negated_conjecture,
% 2.13/1.00      ( v2_pre_topc(sK0) ),
% 2.13/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_558,plain,
% 2.13/1.00      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.13/1.00      | r3_waybel_9(X0,X1,X2)
% 2.13/1.00      | ~ l1_waybel_0(X1,X0)
% 2.13/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.13/1.00      | ~ v7_waybel_0(X1)
% 2.13/1.00      | ~ v4_orders_2(X1)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(X1)
% 2.13/1.00      | ~ l1_pre_topc(X0)
% 2.13/1.00      | sK0 != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_559,plain,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.13/1.00      | r3_waybel_9(sK0,X0,X1)
% 2.13/1.00      | ~ l1_waybel_0(X0,sK0)
% 2.13/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.13/1.00      | ~ v7_waybel_0(X0)
% 2.13/1.00      | ~ v4_orders_2(X0)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | v2_struct_0(sK0)
% 2.13/1.00      | ~ l1_pre_topc(sK0) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_558]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_563,plain,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.13/1.00      | r3_waybel_9(sK0,X0,X1)
% 2.13/1.00      | ~ l1_waybel_0(X0,sK0)
% 2.13/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.13/1.00      | ~ v7_waybel_0(X0)
% 2.13/1.00      | ~ v4_orders_2(X0)
% 2.13/1.00      | v2_struct_0(X0) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_559,c_29,c_27]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_982,plain,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.13/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.00      | ~ l1_waybel_0(X0,sK0)
% 2.13/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.13/1.00      | ~ v7_waybel_0(X0)
% 2.13/1.00      | ~ v4_orders_2(X0)
% 2.13/1.00      | v2_struct_0(X0)
% 2.13/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 2.13/1.00      | sK2 != X1
% 2.13/1.00      | sK0 != sK0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_226,c_563]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_983,plain,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.00      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.13/1.00      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 2.13/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_982]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_21,negated_conjecture,
% 2.13/1.00      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 2.13/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_985,plain,
% 2.13/1.00      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.13/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.00      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.13/1.00      inference(global_propositional_subsumption,[status(thm)],[c_983,c_21]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_986,plain,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.00      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.13/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.13/1.00      inference(renaming,[status(thm)],[c_985]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1022,plain,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | v2_struct_0(X2)
% 2.13/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | ~ l1_struct_0(X2)
% 2.13/1.00      | v1_xboole_0(X1)
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 2.13/1.00      | sK0 != X2 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_986]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1023,plain,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | v2_struct_0(sK0)
% 2.13/1.00      | ~ l1_struct_0(sK0)
% 2.13/1.00      | v1_xboole_0(X1)
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 2.13/1.00      inference(unflattening,[status(thm)],[c_1022]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_73,plain,
% 2.13/1.00      ( ~ l1_pre_topc(sK0) | l1_struct_0(sK0) ),
% 2.13/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1027,plain,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | v1_xboole_0(X1)
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 2.13/1.00      inference(global_propositional_subsumption,
% 2.13/1.00                [status(thm)],
% 2.13/1.00                [c_1023,c_29,c_27,c_73]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1870,plain,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.00      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.00      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.00      | v1_xboole_0(X1)
% 2.13/1.00      | v1_xboole_0(X0)
% 2.13/1.00      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 2.13/1.00      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 2.13/1.00      | sK1 != X0 ),
% 2.13/1.00      inference(resolution_lifted,[status(thm)],[c_1027,c_23]) ).
% 2.13/1.00  
% 2.13/1.00  cnf(c_1871,plain,
% 2.13/1.00      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.00      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.00      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | v1_xboole_0(sK1)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_1870]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1875,plain,
% 2.13/1.01      ( v1_xboole_0(X0)
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1871,c_26]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1876,plain,
% 2.13/1.01      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(renaming,[status(thm)],[c_1875]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_2219,plain,
% 2.13/1.01      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.01      | sK1 != sK1 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_1876]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_3090,plain,
% 2.13/1.01      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_2219]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_3913,plain,
% 2.13/1.01      ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | ~ r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | sP0_iProver_split ),
% 2.13/1.01      inference(splitting,
% 2.13/1.01                [splitting(split),new_symbols(definition,[])],
% 2.13/1.01                [c_3090]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4409,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) != iProver_top
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 2.13/1.01      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 2.13/1.01      | sP0_iProver_split = iProver_top ),
% 2.13/1.01      inference(predicate_to_equality,[status(thm)],[c_3913]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_18,plain,
% 2.13/1.01      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))))
% 2.13/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.13/1.01      | v2_struct_0(X1)
% 2.13/1.01      | ~ l1_struct_0(X1)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0 ),
% 2.13/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_474,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(k2_struct_0(X1))))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1))))))
% 2.13/1.01      | v2_struct_0(X1)
% 2.13/1.01      | ~ l1_struct_0(X1)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k2_yellow19(X1,k3_yellow19(X1,k2_struct_0(X1),X0)) = X0
% 2.13/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X1)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.13/1.01      | sK1 != X0 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_475,plain,
% 2.13/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.13/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.13/1.01      | v2_struct_0(X0)
% 2.13/1.01      | ~ l1_struct_0(X0)
% 2.13/1.01      | v1_xboole_0(sK1)
% 2.13/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 2.13/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_474]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_479,plain,
% 2.13/1.01      ( ~ l1_struct_0(X0)
% 2.13/1.01      | v2_struct_0(X0)
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.13/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.13/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.13/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 2.13/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.13/1.01      inference(global_propositional_subsumption,[status(thm)],[c_475,c_26]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_480,plain,
% 2.13/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.13/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.13/1.01      | v2_struct_0(X0)
% 2.13/1.01      | ~ l1_struct_0(X0)
% 2.13/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 2.13/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.13/1.01      inference(renaming,[status(thm)],[c_479]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1380,plain,
% 2.13/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.13/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(X0))))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0))))))
% 2.13/1.01      | v2_struct_0(X0)
% 2.13/1.01      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),sK1)) = sK1
% 2.13/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(X0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.13/1.01      | sK0 != X0 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_480,c_654]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1381,plain,
% 2.13/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.13/1.01      | ~ v13_waybel_0(sK1,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))
% 2.13/1.01      | v2_struct_0(sK0)
% 2.13/1.01      | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 2.13/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_1380]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1383,plain,
% 2.13/1.01      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1
% 2.13/1.01      | u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) != u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
% 2.13/1.01      inference(global_propositional_subsumption,
% 2.13/1.01                [status(thm)],
% 2.13/1.01                [c_1381,c_29,c_24,c_23,c_22]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_3098,plain,
% 2.13/1.01      ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = sK1 ),
% 2.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_1383]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4526,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,sK1,sK2) != iProver_top
% 2.13/1.01      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 2.13/1.01      | sP0_iProver_split = iProver_top ),
% 2.13/1.01      inference(light_normalisation,[status(thm)],[c_4409,c_3098]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_20,negated_conjecture,
% 2.13/1.01      ( r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 2.13/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_228,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
% 2.13/1.01      inference(prop_impl,[status(thm)],[c_20]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_17,plain,
% 2.13/1.01      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.13/1.01      | ~ r3_waybel_9(X0,X1,X2)
% 2.13/1.01      | ~ l1_waybel_0(X1,X0)
% 2.13/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.13/1.01      | ~ v7_waybel_0(X1)
% 2.13/1.01      | ~ v4_orders_2(X1)
% 2.13/1.01      | v2_struct_0(X0)
% 2.13/1.01      | v2_struct_0(X1)
% 2.13/1.01      | ~ v2_pre_topc(X0)
% 2.13/1.01      | ~ l1_pre_topc(X0) ),
% 2.13/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_525,plain,
% 2.13/1.01      ( r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
% 2.13/1.01      | ~ r3_waybel_9(X0,X1,X2)
% 2.13/1.01      | ~ l1_waybel_0(X1,X0)
% 2.13/1.01      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.13/1.01      | ~ v7_waybel_0(X1)
% 2.13/1.01      | ~ v4_orders_2(X1)
% 2.13/1.01      | v2_struct_0(X0)
% 2.13/1.01      | v2_struct_0(X1)
% 2.13/1.01      | ~ l1_pre_topc(X0)
% 2.13/1.01      | sK0 != X0 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_526,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.13/1.01      | ~ r3_waybel_9(sK0,X0,X1)
% 2.13/1.01      | ~ l1_waybel_0(X0,sK0)
% 2.13/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.13/1.01      | ~ v7_waybel_0(X0)
% 2.13/1.01      | ~ v4_orders_2(X0)
% 2.13/1.01      | v2_struct_0(X0)
% 2.13/1.01      | v2_struct_0(sK0)
% 2.13/1.01      | ~ l1_pre_topc(sK0) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_525]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_530,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.13/1.01      | ~ r3_waybel_9(sK0,X0,X1)
% 2.13/1.01      | ~ l1_waybel_0(X0,sK0)
% 2.13/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.13/1.01      | ~ v7_waybel_0(X0)
% 2.13/1.01      | ~ v4_orders_2(X0)
% 2.13/1.01      | v2_struct_0(X0) ),
% 2.13/1.01      inference(global_propositional_subsumption,
% 2.13/1.01                [status(thm)],
% 2.13/1.01                [c_526,c_29,c_27]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_956,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ l1_waybel_0(X0,sK0)
% 2.13/1.01      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 2.13/1.01      | ~ v7_waybel_0(X0)
% 2.13/1.01      | ~ v4_orders_2(X0)
% 2.13/1.01      | v2_struct_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != X0
% 2.13/1.01      | sK2 != X1
% 2.13/1.01      | sK0 != sK0 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_228,c_530]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_957,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.13/1.01      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_956]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_959,plain,
% 2.13/1.01      ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.13/1.01      inference(global_propositional_subsumption,[status(thm)],[c_957,c_21]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_960,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
% 2.13/1.01      inference(renaming,[status(thm)],[c_959]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1070,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(X2)
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ l1_struct_0(X2)
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(X2,X1,X0)
% 2.13/1.01      | sK0 != X2 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_960]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1071,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(sK0)
% 2.13/1.01      | ~ l1_struct_0(sK0)
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_1070]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1075,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0) ),
% 2.13/1.01      inference(global_propositional_subsumption,
% 2.13/1.01                [status(thm)],
% 2.13/1.01                [c_1071,c_29,c_27,c_73]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1825,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X1,X0)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 2.13/1.01      | sK1 != X0 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_1075,c_23]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1826,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | v1_xboole_0(sK1)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_1825]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1830,plain,
% 2.13/1.01      ( v1_xboole_0(X0)
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1826,c_26]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1831,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(renaming,[status(thm)],[c_1830]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_2257,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.01      | sK1 != sK1 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_1831]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_3086,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_2257]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_3914,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2)
% 2.13/1.01      | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
% 2.13/1.01      | sP0_iProver_split ),
% 2.13/1.01      inference(splitting,
% 2.13/1.01                [splitting(split),new_symbols(definition,[])],
% 2.13/1.01                [c_3086]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4411,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) = iProver_top
% 2.13/1.01      | r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 2.13/1.01      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 2.13/1.01      | sP0_iProver_split = iProver_top ),
% 2.13/1.01      inference(predicate_to_equality,[status(thm)],[c_3914]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4502,plain,
% 2.13/1.01      ( r1_waybel_7(sK0,sK1,sK2) = iProver_top
% 2.13/1.01      | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 2.13/1.01      | sP0_iProver_split = iProver_top ),
% 2.13/1.01      inference(light_normalisation,[status(thm)],[c_4411,c_3098]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4532,plain,
% 2.13/1.01      ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 2.13/1.01      | sP0_iProver_split = iProver_top ),
% 2.13/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4526,c_4502]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4420,plain,
% 2.13/1.01      ( m1_subset_1(sK2,u1_struct_0(sK0)) = iProver_top ),
% 2.13/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4433,plain,
% 2.13/1.01      ( m1_subset_1(sK2,k2_struct_0(sK0)) = iProver_top ),
% 2.13/1.01      inference(light_normalisation,[status(thm)],[c_4420,c_1392]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_8,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.13/1.01      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.01      | v2_struct_0(X1)
% 2.13/1.01      | ~ v2_pre_topc(X1)
% 2.13/1.01      | ~ l1_pre_topc(X1) ),
% 2.13/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_612,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.13/1.01      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.13/1.01      | v2_struct_0(X1)
% 2.13/1.01      | ~ l1_pre_topc(X1)
% 2.13/1.01      | sK0 != X1 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_8,c_28]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_613,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.13/1.01      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | v2_struct_0(sK0)
% 2.13/1.01      | ~ l1_pre_topc(sK0) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_612]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_617,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.13/1.01      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.13/1.01      inference(global_propositional_subsumption,
% 2.13/1.01                [status(thm)],
% 2.13/1.01                [c_613,c_29,c_27]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4415,plain,
% 2.13/1.01      ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 2.13/1.01      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.13/1.01      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4448,plain,
% 2.13/1.01      ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
% 2.13/1.01      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 2.13/1.01      inference(light_normalisation,[status(thm)],[c_4415,c_1392]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5,plain,
% 2.13/1.01      ( ~ r2_hidden(X0,X1)
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.13/1.01      | ~ v1_xboole_0(X2) ),
% 2.13/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_9,plain,
% 2.13/1.01      ( r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.13/1.01      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.13/1.01      | v2_struct_0(X1)
% 2.13/1.01      | ~ v2_pre_topc(X1)
% 2.13/1.01      | ~ l1_pre_topc(X1) ),
% 2.13/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_404,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.13/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.13/1.01      | v2_struct_0(X1)
% 2.13/1.01      | ~ v2_pre_topc(X1)
% 2.13/1.01      | ~ l1_pre_topc(X1)
% 2.13/1.01      | ~ v1_xboole_0(X3)
% 2.13/1.01      | X0 != X4
% 2.13/1.01      | k1_connsp_2(X1,X0) != X2 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_405,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.13/1.01      | ~ m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(X2))
% 2.13/1.01      | v2_struct_0(X1)
% 2.13/1.01      | ~ v2_pre_topc(X1)
% 2.13/1.01      | ~ l1_pre_topc(X1)
% 2.13/1.01      | ~ v1_xboole_0(X2) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_404]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_591,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.13/1.01      | ~ m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(X2))
% 2.13/1.01      | v2_struct_0(X1)
% 2.13/1.01      | ~ l1_pre_topc(X1)
% 2.13/1.01      | ~ v1_xboole_0(X2)
% 2.13/1.01      | sK0 != X1 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_405,c_28]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_592,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.13/1.01      | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1))
% 2.13/1.01      | v2_struct_0(sK0)
% 2.13/1.01      | ~ l1_pre_topc(sK0)
% 2.13/1.01      | ~ v1_xboole_0(X1) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_591]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_596,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
% 2.13/1.01      | ~ m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1))
% 2.13/1.01      | ~ v1_xboole_0(X1) ),
% 2.13/1.01      inference(global_propositional_subsumption,
% 2.13/1.01                [status(thm)],
% 2.13/1.01                [c_592,c_29,c_27]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4416,plain,
% 2.13/1.01      ( m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 2.13/1.01      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1)) != iProver_top
% 2.13/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.13/1.01      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4459,plain,
% 2.13/1.01      ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
% 2.13/1.01      | m1_subset_1(k1_connsp_2(sK0,X0),k1_zfmisc_1(X1)) != iProver_top
% 2.13/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.13/1.01      inference(light_normalisation,[status(thm)],[c_4416,c_1392]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4680,plain,
% 2.13/1.01      ( m1_subset_1(X0,k2_struct_0(sK0)) != iProver_top
% 2.13/1.01      | v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
% 2.13/1.01      inference(superposition,[status(thm)],[c_4448,c_4459]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5126,plain,
% 2.13/1.01      ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
% 2.13/1.01      inference(superposition,[status(thm)],[c_4433,c_4680]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_15,plain,
% 2.13/1.01      ( ~ v1_subset_1(X0,u1_struct_0(k3_lattice3(k1_lattice3(X1))))
% 2.13/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | v2_struct_0(X2)
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.13/1.01      | ~ l1_struct_0(X2)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | v1_xboole_0(X1) ),
% 2.13/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_13,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | v2_struct_0(X2)
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.13/1.01      | ~ l1_struct_0(X2)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | v1_xboole_0(X1) ),
% 2.13/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_169,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | v2_struct_0(X2)
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.13/1.01      | ~ l1_struct_0(X2)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | v1_xboole_0(X1) ),
% 2.13/1.01      inference(global_propositional_subsumption,[status(thm)],[c_15,c_13]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_170,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | v2_struct_0(X2)
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.13/1.01      | ~ l1_struct_0(X2)
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0) ),
% 2.13/1.01      inference(renaming,[status(thm)],[c_169]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1396,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | v2_struct_0(X2)
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(X2,X1,X0))
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | sK0 != X2 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_170,c_654]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1397,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 2.13/1.01      | v2_struct_0(sK0)
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_1396]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1401,plain,
% 2.13/1.01      ( ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0) ),
% 2.13/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1397,c_29]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1402,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0) ),
% 2.13/1.01      inference(renaming,[status(thm)],[c_1401]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1795,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(sK0,X1,X0))
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 2.13/1.01      | sK1 != X0 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_1402,c_23]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1796,plain,
% 2.13/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | v1_xboole_0(sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_1795]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1800,plain,
% 2.13/1.01      ( v1_xboole_0(X0)
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1796,c_26]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1801,plain,
% 2.13/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(renaming,[status(thm)],[c_1800]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_2295,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.01      | sK1 != sK1 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_1801]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_3082,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ v2_struct_0(k3_yellow19(sK0,X0,sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_2295]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4413,plain,
% 2.13/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.13/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,X0,sK1)) != iProver_top
% 2.13/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.13/1.01      inference(predicate_to_equality,[status(thm)],[c_3082]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4477,plain,
% 2.13/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,X0,sK1)) != iProver_top
% 2.13/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.13/1.01      inference(light_normalisation,[status(thm)],[c_4413,c_1392]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4985,plain,
% 2.13/1.01      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 2.13/1.01      inference(equality_resolution,[status(thm)],[c_4477]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5431,plain,
% 2.13/1.01      ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top
% 2.13/1.01      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 2.13/1.01      inference(global_propositional_subsumption,
% 2.13/1.01                [status(thm)],
% 2.13/1.01                [c_4985,c_37,c_5126]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5432,plain,
% 2.13/1.01      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.01      | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) != iProver_top ),
% 2.13/1.01      inference(renaming,[status(thm)],[c_5431]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_3912,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.01      | ~ sP0_iProver_split ),
% 2.13/1.01      inference(splitting,
% 2.13/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.13/1.01                [c_3090]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4410,plain,
% 2.13/1.01      ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.13/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.13/1.01      | v1_xboole_0(X0) = iProver_top
% 2.13/1.01      | sP0_iProver_split != iProver_top ),
% 2.13/1.01      inference(predicate_to_equality,[status(thm)],[c_3912]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4488,plain,
% 2.13/1.01      ( k3_yellow19(sK0,k2_struct_0(sK0),sK1) != k3_yellow19(sK0,X0,sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.13/1.01      | v1_xboole_0(X0) = iProver_top
% 2.13/1.01      | sP0_iProver_split != iProver_top ),
% 2.13/1.01      inference(light_normalisation,[status(thm)],[c_4410,c_1392]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4994,plain,
% 2.13/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(k2_struct_0(sK0)))
% 2.13/1.01      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 2.13/1.01      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
% 2.13/1.01      | sP0_iProver_split != iProver_top ),
% 2.13/1.01      inference(equality_resolution,[status(thm)],[c_4488]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5437,plain,
% 2.13/1.01      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 2.13/1.01      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
% 2.13/1.01      | sP0_iProver_split != iProver_top ),
% 2.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_4994]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5439,plain,
% 2.13/1.01      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.01      | sP0_iProver_split != iProver_top ),
% 2.13/1.01      inference(global_propositional_subsumption,
% 2.13/1.01                [status(thm)],
% 2.13/1.01                [c_5437,c_37,c_5126]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_12,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.13/1.01      | v2_struct_0(X2)
% 2.13/1.01      | ~ l1_struct_0(X2)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | v1_xboole_0(X1) ),
% 2.13/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1429,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | v4_orders_2(k3_yellow19(X2,X1,X0))
% 2.13/1.01      | v2_struct_0(X2)
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | sK0 != X2 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_654]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1430,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 2.13/1.01      | v2_struct_0(sK0)
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_1429]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1434,plain,
% 2.13/1.01      ( v4_orders_2(k3_yellow19(sK0,X1,X0))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0) ),
% 2.13/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1430,c_29]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1435,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ v13_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0) ),
% 2.13/1.01      inference(renaming,[status(thm)],[c_1434]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1765,plain,
% 2.13/1.01      ( ~ v2_waybel_0(X0,k3_lattice3(k1_lattice3(X1)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X1)))))
% 2.13/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,X1,X0))
% 2.13/1.01      | v1_xboole_0(X1)
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X1))
% 2.13/1.01      | sK1 != X0 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_1435,c_23]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1766,plain,
% 2.13/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | v1_xboole_0(sK1)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(unflattening,[status(thm)],[c_1765]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1770,plain,
% 2.13/1.01      ( v1_xboole_0(X0)
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1766,c_26]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_1771,plain,
% 2.13/1.01      ( ~ v2_waybel_0(sK1,k3_lattice3(k1_lattice3(X0)))
% 2.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(renaming,[status(thm)],[c_1770]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_2318,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.01      | sK1 != sK1 ),
% 2.13/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_1771]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_3078,plain,
% 2.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.13/1.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,X0,sK1))
% 2.13/1.01      | v1_xboole_0(X0)
% 2.13/1.01      | k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0)) ),
% 2.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_2318]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4414,plain,
% 2.13/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.13/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,X0,sK1)) = iProver_top
% 2.13/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.13/1.01      inference(predicate_to_equality,[status(thm)],[c_3078]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4466,plain,
% 2.13/1.01      ( k3_lattice3(k1_lattice3(k2_struct_0(sK0))) != k3_lattice3(k1_lattice3(X0))
% 2.13/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) != iProver_top
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,X0,sK1)) = iProver_top
% 2.13/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.13/1.01      inference(light_normalisation,[status(thm)],[c_4414,c_1392]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5055,plain,
% 2.13/1.01      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) != iProver_top
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 2.13/1.01      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 2.13/1.01      inference(equality_resolution,[status(thm)],[c_4466]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5524,plain,
% 2.13/1.01      ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top
% 2.13/1.01      | m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 2.13/1.01      inference(global_propositional_subsumption,
% 2.13/1.01                [status(thm)],
% 2.13/1.01                [c_5055,c_37,c_5126]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5525,plain,
% 2.13/1.01      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 2.13/1.01      | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) = iProver_top ),
% 2.13/1.01      inference(renaming,[status(thm)],[c_5524]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5534,plain,
% 2.13/1.01      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 2.13/1.01      inference(global_propositional_subsumption,
% 2.13/1.01                [status(thm)],
% 2.13/1.01                [c_5532,c_37,c_4532,c_5126,c_5432,c_5439,c_5525]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5539,plain,
% 2.13/1.01      ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) != iProver_top ),
% 2.13/1.01      inference(superposition,[status(thm)],[c_4422,c_5534]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f92]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_4423,plain,
% 2.13/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 2.13/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.13/1.01  
% 2.13/1.01  cnf(c_5600,plain,
% 2.13/1.01      ( $false ),
% 2.13/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5539,c_4423]) ).
% 2.13/1.01  
% 2.13/1.01  
% 2.13/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.13/1.01  
% 2.13/1.01  ------                               Statistics
% 2.13/1.01  
% 2.13/1.01  ------ General
% 2.13/1.01  
% 2.13/1.01  abstr_ref_over_cycles:                  0
% 2.13/1.01  abstr_ref_under_cycles:                 0
% 2.13/1.01  gc_basic_clause_elim:                   0
% 2.13/1.01  forced_gc_time:                         0
% 2.13/1.01  parsing_time:                           0.009
% 2.13/1.01  unif_index_cands_time:                  0.
% 2.13/1.01  unif_index_add_time:                    0.
% 2.13/1.01  orderings_time:                         0.
% 2.13/1.01  out_proof_time:                         0.014
% 2.13/1.01  total_time:                             0.177
% 2.13/1.01  num_of_symbols:                         59
% 2.13/1.01  num_of_terms:                           2242
% 2.13/1.01  
% 2.13/1.01  ------ Preprocessing
% 2.13/1.01  
% 2.13/1.01  num_of_splits:                          2
% 2.13/1.01  num_of_split_atoms:                     1
% 2.13/1.01  num_of_reused_defs:                     1
% 2.13/1.01  num_eq_ax_congr_red:                    14
% 2.13/1.01  num_of_sem_filtered_clauses:            1
% 2.13/1.01  num_of_subtypes:                        0
% 2.13/1.01  monotx_restored_types:                  0
% 2.13/1.01  sat_num_of_epr_types:                   0
% 2.13/1.01  sat_num_of_non_cyclic_types:            0
% 2.13/1.01  sat_guarded_non_collapsed_types:        0
% 2.13/1.01  num_pure_diseq_elim:                    0
% 2.13/1.01  simp_replaced_by:                       0
% 2.13/1.01  res_preprocessed:                       114
% 2.13/1.01  prep_upred:                             0
% 2.13/1.01  prep_unflattend:                        53
% 2.13/1.01  smt_new_axioms:                         0
% 2.13/1.01  pred_elim_cands:                        7
% 2.13/1.01  pred_elim:                              9
% 2.13/1.01  pred_elim_cl:                           11
% 2.13/1.01  pred_elim_cycles:                       26
% 2.13/1.01  merged_defs:                            10
% 2.13/1.01  merged_defs_ncl:                        0
% 2.13/1.01  bin_hyper_res:                          10
% 2.13/1.01  prep_cycles:                            4
% 2.13/1.01  pred_elim_time:                         0.089
% 2.13/1.01  splitting_time:                         0.
% 2.13/1.01  sem_filter_time:                        0.
% 2.13/1.01  monotx_time:                            0.
% 2.13/1.01  subtype_inf_time:                       0.
% 2.13/1.01  
% 2.13/1.01  ------ Problem properties
% 2.13/1.01  
% 2.13/1.01  clauses:                                19
% 2.13/1.01  conjectures:                            4
% 2.13/1.01  epr:                                    4
% 2.13/1.01  horn:                                   15
% 2.13/1.01  ground:                                 8
% 2.13/1.01  unary:                                  7
% 2.13/1.01  binary:                                 3
% 2.13/1.01  lits:                                   59
% 2.13/1.01  lits_eq:                                11
% 2.13/1.01  fd_pure:                                0
% 2.13/1.01  fd_pseudo:                              0
% 2.13/1.01  fd_cond:                                0
% 2.13/1.01  fd_pseudo_cond:                         1
% 2.13/1.01  ac_symbols:                             0
% 2.13/1.01  
% 2.13/1.01  ------ Propositional Solver
% 2.13/1.01  
% 2.13/1.01  prop_solver_calls:                      28
% 2.13/1.01  prop_fast_solver_calls:                 1883
% 2.13/1.01  smt_solver_calls:                       0
% 2.13/1.01  smt_fast_solver_calls:                  0
% 2.13/1.01  prop_num_of_clauses:                    976
% 2.13/1.01  prop_preprocess_simplified:             3799
% 2.13/1.01  prop_fo_subsumed:                       42
% 2.13/1.01  prop_solver_time:                       0.
% 2.13/1.01  smt_solver_time:                        0.
% 2.13/1.01  smt_fast_solver_time:                   0.
% 2.13/1.01  prop_fast_solver_time:                  0.
% 2.13/1.01  prop_unsat_core_time:                   0.
% 2.13/1.01  
% 2.13/1.01  ------ QBF
% 2.13/1.01  
% 2.13/1.01  qbf_q_res:                              0
% 2.13/1.01  qbf_num_tautologies:                    0
% 2.13/1.01  qbf_prep_cycles:                        0
% 2.13/1.01  
% 2.13/1.01  ------ BMC1
% 2.13/1.01  
% 2.13/1.01  bmc1_current_bound:                     -1
% 2.13/1.01  bmc1_last_solved_bound:                 -1
% 2.13/1.01  bmc1_unsat_core_size:                   -1
% 2.13/1.01  bmc1_unsat_core_parents_size:           -1
% 2.13/1.01  bmc1_merge_next_fun:                    0
% 2.13/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.13/1.01  
% 2.13/1.01  ------ Instantiation
% 2.13/1.01  
% 2.13/1.01  inst_num_of_clauses:                    198
% 2.13/1.01  inst_num_in_passive:                    39
% 2.13/1.01  inst_num_in_active:                     150
% 2.13/1.01  inst_num_in_unprocessed:                9
% 2.13/1.01  inst_num_of_loops:                      160
% 2.13/1.01  inst_num_of_learning_restarts:          0
% 2.13/1.01  inst_num_moves_active_passive:          6
% 2.13/1.01  inst_lit_activity:                      0
% 2.13/1.01  inst_lit_activity_moves:                0
% 2.13/1.01  inst_num_tautologies:                   0
% 2.13/1.01  inst_num_prop_implied:                  0
% 2.13/1.01  inst_num_existing_simplified:           0
% 2.13/1.01  inst_num_eq_res_simplified:             0
% 2.13/1.01  inst_num_child_elim:                    0
% 2.13/1.01  inst_num_of_dismatching_blockings:      64
% 2.13/1.01  inst_num_of_non_proper_insts:           287
% 2.13/1.01  inst_num_of_duplicates:                 0
% 2.13/1.01  inst_inst_num_from_inst_to_res:         0
% 2.13/1.01  inst_dismatching_checking_time:         0.
% 2.13/1.01  
% 2.13/1.01  ------ Resolution
% 2.13/1.01  
% 2.13/1.01  res_num_of_clauses:                     0
% 2.13/1.01  res_num_in_passive:                     0
% 2.13/1.01  res_num_in_active:                      0
% 2.13/1.01  res_num_of_loops:                       118
% 2.13/1.01  res_forward_subset_subsumed:            37
% 2.13/1.01  res_backward_subset_subsumed:           4
% 2.13/1.01  res_forward_subsumed:                   1
% 2.13/1.01  res_backward_subsumed:                  0
% 2.13/1.01  res_forward_subsumption_resolution:     2
% 2.13/1.01  res_backward_subsumption_resolution:    0
% 2.13/1.01  res_clause_to_clause_subsumption:       320
% 2.13/1.01  res_orphan_elimination:                 0
% 2.13/1.01  res_tautology_del:                      57
% 2.13/1.01  res_num_eq_res_simplified:              6
% 2.13/1.01  res_num_sel_changes:                    0
% 2.13/1.01  res_moves_from_active_to_pass:          0
% 2.13/1.01  
% 2.13/1.01  ------ Superposition
% 2.13/1.01  
% 2.13/1.01  sup_time_total:                         0.
% 2.13/1.01  sup_time_generating:                    0.
% 2.13/1.01  sup_time_sim_full:                      0.
% 2.13/1.01  sup_time_sim_immed:                     0.
% 2.13/1.01  
% 2.13/1.01  sup_num_of_clauses:                     29
% 2.13/1.01  sup_num_in_active:                      27
% 2.13/1.01  sup_num_in_passive:                     2
% 2.13/1.01  sup_num_of_loops:                       30
% 2.13/1.01  sup_fw_superposition:                   11
% 2.13/1.01  sup_bw_superposition:                   4
% 2.13/1.01  sup_immediate_simplified:               0
% 2.13/1.01  sup_given_eliminated:                   0
% 2.13/1.01  comparisons_done:                       0
% 2.13/1.01  comparisons_avoided:                    0
% 2.13/1.01  
% 2.13/1.01  ------ Simplifications
% 2.13/1.01  
% 2.13/1.01  
% 2.13/1.01  sim_fw_subset_subsumed:                 0
% 2.13/1.01  sim_bw_subset_subsumed:                 5
% 2.13/1.01  sim_fw_subsumed:                        0
% 2.13/1.01  sim_bw_subsumed:                        1
% 2.13/1.01  sim_fw_subsumption_res:                 2
% 2.13/1.01  sim_bw_subsumption_res:                 0
% 2.13/1.01  sim_tautology_del:                      1
% 2.13/1.01  sim_eq_tautology_del:                   1
% 2.13/1.01  sim_eq_res_simp:                        2
% 2.13/1.01  sim_fw_demodulated:                     0
% 2.13/1.01  sim_bw_demodulated:                     0
% 2.13/1.01  sim_light_normalised:                   10
% 2.13/1.01  sim_joinable_taut:                      0
% 2.13/1.01  sim_joinable_simp:                      0
% 2.13/1.01  sim_ac_normalised:                      0
% 2.13/1.01  sim_smt_subsumption:                    0
% 2.13/1.01  
%------------------------------------------------------------------------------
